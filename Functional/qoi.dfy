/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */

include "spec.dfy"
include "specbit.dfy"


// Folosim liste înlănțuite pentru a adăuga elemente la început în O(1), reducând complexitatea totală la O(N).
datatype OpChain = EmptyOp | LinkOp(op: Op, next: OpChain)
datatype ByteChain = EmptyByte | LinkByte(data: seq<byte>, next: ByteChain)



// Metodă pentru inversarea listei de operațiuni (Ops).
// Deoarece adăugăm elemente la începutul listei (pentru viteză), lista finală e inversată.
// Această metodă o pune în ordinea corectă.
method ReverseOpChain(chain: OpChain) returns (rev: OpChain)
  // Garantăm că numărul de elemente rămâne neschimbat.
  ensures |OpChainToSeq(rev)| == |OpChainToSeq(chain)|
{
  rev := EmptyOp;
  var current := chain;
  while current != EmptyOp

    // 'decreases': Demonstrează terminarea buclei (lungimea listei scade la fiecare pas).
    decreases current
    
    // Lungimea listei construite (rev) + Lungimea listei rămase (current) = Totalul inițial.
    invariant |OpChainToSeq(rev)| + |OpChainToSeq(current)| == |OpChainToSeq(chain)|
  {
    match current {
      case LinkOp(op, next) =>
        rev := LinkOp(op, rev); // Mutăm elementul în lista inversată
        current := next; // Avansăm
      case EmptyOp => 
        break;
    }
  }
}


// Metodă pentru "aplatizarea" (Flatten) listei de bucăți de memorie într-un singur șir continuu.
method FlattenBytesIterative(chain: ByteChain) returns (res: seq<byte>)
  // Postconditie: Lungimea rezultatului este suma lungimilor din lant
  ensures |res| == ByteChainLength(chain)
{
  res := [];
  var current := chain;
  while current != EmptyByte
    decreases current
    // Invariant: lungimea rezultatului curent + ce a mai ramas de procesat = total
    invariant |res| + ByteChainLength(current) == ByteChainLength(chain)
  {
    match current {
      case LinkByte(d, next) =>
        res := d + res;     // Concatenare
        current := next;
      case EmptyByte =>
        break;
    }
  }
}

// Check if two pixels are close enough to use delta encoding (type 1)
function canDiff(curr : RGBA, prev : RGBA) : Option<RGBDiff>
  ensures forall dr, dg, db : Diff :: canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==>
  curr.r == add_byte(prev.r, byte_from(dr as int)) && 
  curr.g == add_byte(prev.g, byte_from(dg as int)) && 
  curr.b == add_byte(prev.b, byte_from(db as int)) &&
  curr.a == prev.a
{
  var dr : int := curr.r as int - prev.r as int;
  var dg : int := curr.g as int - prev.g as int;
  var db : int := curr.b as int - prev.b as int;
  var da : int := curr.a as int - prev.a as int;
  if (-2 <= dr <= 1 && -2 <= dg <= 1 && -2 <= db <= 1 && da == 0) then
    Some(RGBDiff(dr as Diff, dg as Diff, db as Diff))
  else
    None
}

// Check if two pixels are close enough to use delta encoding (type 2)
function canLuma(curr : RGBA, prev : RGBA) : Option<RGBLuma>
  ensures forall luma : RGBLuma// , dgr : Diff16 :: forall dg : Diff64 :: forall dgb : Diff16
  ::
  canLuma(curr, prev) == Some(luma) ==>
  curr.r == add_byte(add_byte(prev.r, byte_from(luma.dg as int)), byte_from(luma.dr as int)) && 
  curr.g == add_byte(prev.g, byte_from(luma.dg as int)) && 
  curr.b == add_byte(add_byte(prev.b, byte_from(luma.dg as int)), byte_from(luma.db as int))  && 
  curr.a == prev.a
{
  var dr : int := curr.r as int - prev.r as int;
  var dg : int := curr.g as int - prev.g as int;
  var db : int := curr.b as int - prev.b as int;
  var da : int := curr.a as int - prev.a as int;
  if (-32 <= dg <= 31 && -8 <= (dr - dg) <= 7 && -8 <= (db - dg) <= 7 && da == 0) then
    (
    assert curr.a == prev.a;
    assert curr.g == add_byte(prev.g, byte_from((dg as Diff64) as int));
    assert curr.r == add_byte(add_byte(prev.r, byte_from((dg as Diff64) as int)), byte_from((dr - dg) as int));
    assert curr.b == add_byte(add_byte(prev.b, byte_from((dg as Diff64) as int)), byte_from((db - dg) as int));
    Some(RGBLuma((dr - dg) as Diff16, dg as Diff64, (db - dg) as Diff16))
      )
  else
    None
}

// Codifică toți pixelii imaginii într-un lanț de operațiuni (OpChain).
method encodeAEI(image : seq<RGBA>) returns (chain : OpChain)
{
  chain := EmptyOp;

  // Inițializare conform spec QOI: pixel precedent este negru transparent (0,0,0,0), dar alpha start e 255.
  var prev : RGBA := RGBA(r := 0, g := 0, b := 0, a := 255);

  // Array de indexare (cache) de 64 elemente, inițializat cu 0.
  var index : array<RGBA> := new RGBA[64](i => RGBA(r := 0, g := 0, b := 0, a := 255));

  var i : int := 0;
  var wh : int := |image|;
  var run := 0; // Contor pentru QOI_OP_RUN
  
  while (i < wh)
    invariant 0 <= i <= wh
    invariant 0 <= run <= 62 // Run nu poate depăși 62 conform standardului
    decreases wh - i  // Demonstrează că bucla se termină
  {
    var curr := image[i];

    // 1. Verificare QOI_OP_RUN (Pixel identic cu cel precedent)
    if curr == prev {
      run := run + 1;
      if run == 62 {
        chain := LinkOp(OpRun(62), chain);
        run := 0;
      }
    } 
    else {
      // Dacă seria de pixeli identici s-a terminat, scriem operațiunea RUN
      if run > 0 {
        chain := LinkOp(OpRun(run as Size), chain);
        run := 0;
      }

      // 2. Verificare QOI_OP_INDEX (Pixel existent deja în cache)
      var h := hashRGBA(curr);
      if index[h] == curr {
         chain := LinkOp(OpIndex(h as Index64), chain);
      } 
      else {
        // Actualizăm cache-ul
        index[h] := curr;

        // 3. Încercăm QOI_OP_DIFF (Diferențe mici)
        if canDiff(curr, prev).Some? {
           chain := LinkOp(OpDiff(canDiff(curr, prev).some), chain);
        } 
        // 4. Încercăm QOI_OP_LUMA (Diferențe medii bazate pe verde)
        else if canLuma(curr, prev).Some? {
           chain := LinkOp(OpLuma(canLuma(curr, prev).some), chain);
        } 
        // 5. Încercăm QOI_OP_RGB (Alpha neschimbat, scriem doar RGB)
        else if curr.a == prev.a {
           chain := LinkOp(OpRGB(RGB(curr.r, curr.g, curr.b)), chain);
        } 
        // 6. Fallback QOI_OP_RGBA (Scriem tot pixelul)
        else {
           chain := LinkOp(OpRGBA(curr), chain);
        }
      }
    }
    prev := curr;
    i := i + 1;
  }
  
  // Scriem orice RUN rămas la finalul fișierului
  if run > 0 {
    chain := LinkOp(OpRun(run as Size), chain);
  }
}

// Transformă lanțul de Operațiuni (Abstract) în lanț de Bytes (Concrete).
// Fiecare Op este convertit în 1-5 bytes conform standardului.
method encodeBitSeq_Chain(ops: OpChain) returns (bytes: ByteChain)

// garantam ca returnam un lant valid (implicit prin tip)
  ensures bytes.LinkByte? || bytes.EmptyByte?
{
  bytes := EmptyByte;
  var current := ops;
  
  while current != EmptyOp
    decreases current
  {
    match current {
      case LinkOp(op, next) =>
        var chunk := encodeBits(op);
        bytes := LinkByte(chunk, bytes);
        current := next;
      case EmptyOp => break;
    }
  }
}

// Decodifică un șir de bytes în secvența de Operațiuni.
// Implementat iterativ pentru viteză.
method decodeBitSeq_Iterative(bits: seq<byte>) returns (ops: seq<Op>)
{
  ops := [];
  var i := 0;
  var len := |bits|;
  
  while i < len
    invariant 0 <= i <= len
  {
    var b1 := bits[i];
    
    if b1 == 254 { // RGB
       if i + 4 <= len {
         ops := ops + [ OpRGB(RGB(bits[i+1], bits[i+2], bits[i+3])) ];
         i := i + 4;
       } else { break; }
    } 
    else if b1 == 255 { // RGBA
       if i + 5 <= len {
         ops := ops + [ OpRGBA(RGBA(bits[i+1], bits[i+2], bits[i+3], bits[i+4])) ];
         i := i + 5;
       } else { break; }
    }
    else {
      var tag := b1 / 64;
      if tag == 0 { // INDEX
         ops := ops + [ OpIndex(b1 as Index64) ];
         i := i + 1;
      } 
      else if tag == 1 { // DIFF
         var dr := (((b1 / 16) % 4) as int - 2) as Diff;
         var dg := (((b1 / 4) % 4) as int - 2) as Diff;
         var db := ((b1 % 4) as int - 2) as Diff;
         ops := ops + [ OpDiff(RGBDiff(dr, dg, db)) ];
         i := i + 1;
      }
      else if tag == 2 { // LUMA
         if i + 2 <= len {
            var b2 := bits[i+1];
            var dg := ((b1 % 64) as int - 32) as Diff64;
            var dr_dg := (((b2 / 16) % 16) as int - 8) as Diff16;
            var db_dg := ((b2 % 16) as int - 8) as Diff16;
            ops := ops + [ OpLuma(RGBLuma(dr_dg, dg, db_dg)) ];
            i := i + 2;
         } else { break; }
      }
      else { // RUN
         var run := ((b1 % 64) as int + 1) as Size;
         ops := ops + [ OpRun(run) ];
         i := i + 1;
      }
    }
  }
}


// Reconstruiește imaginea pixel cu pixel din lista de operațiuni.
// Folosește starea internă (prev, index array) pentru a decodifica.
method decodeAEI_PureChain(ops : seq<Op>) returns (chain : ByteChain)
{
  chain := EmptyByte; 
  
  // Starea decodificatorului: Cache gol, pixel anterior negru-transparent
  var index : seq<RGBA> := seq(64, i => RGBA(0, 0, 0, 0));
  var prev := RGBA(0, 0, 0, 255);
  
  var i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |index| == 64 // Important: Array-ul de indexare trebuie să aibă mereu 64 elemente
  {
    var op := ops[i];
    
    // Logica explicita (inlined) pentru viteza
    match op {
       case OpRGB(rgb) =>
          prev := RGBA(rgb.r, rgb.g, rgb.b, prev.a);
          chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
          index := index[hashRGBA(prev) := prev]; 

       case OpRGBA(rgba) =>
          prev := rgba;
          chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
          index := index[hashRGBA(prev) := prev];

       case OpIndex(idx) =>
          prev := index[idx];
          chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
          
       case OpRun(len) =>
          // Repetăm pixelul anterior de 'len' ori
          var chunk := [prev.r, prev.g, prev.b, prev.a];
          var k := 0;
          while k < len as int {
             chain := LinkByte(chunk, chain);
             k := k + 1;
          }

       case OpDiff(diff) =>
          // Aplicăm diferențele mici
          prev := RGBA(
             add_byte(prev.r, byte_from(diff.dr as int)),
             add_byte(prev.g, byte_from(diff.dg as int)),
             add_byte(prev.b, byte_from(diff.db as int)),
             prev.a
          );
          chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
          index := index[hashRGBA(prev) := prev];

       case OpLuma(luma) =>
          // Aplicăm diferențele Luma
          var dg := luma.dg as int;
          var dr := luma.dr as int + dg;
          var db := luma.db as int + dg;
          prev := RGBA(
             add_byte(prev.r, byte_from(dr)),
             add_byte(prev.g, byte_from(dg)),
             add_byte(prev.b, byte_from(db)),
             prev.a
          );
          chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
          index := index[hashRGBA(prev) := prev];
    }
    i := i + 1;
  }
}

  

  

// Interpret a sequence of bytes as a sequence of RGB pixels
function asRGBA3(data : seq<byte>) : seq<RGBA>
  requires |data| % 3 == 0
  ensures toByteStreamRGB(asRGBA3(data)) == data
  ensures |asRGBA3(data)| == |data| / 3
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], 255) ] + asRGBA3(data[3..])
}

// Interpret a sequence of bytes as a sequence of RGBA pixels
function asRGBA4(data : seq<byte>) : seq<RGBA>
  requires |data| % 4 == 0
  ensures toByteStreamRGBA(asRGBA4(data)) == data
  ensures |asRGBA4(data)| == |data| / 4
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], data[3]) ] + asRGBA4(data[4..])
}

// Interpret a sequence of bytes as a sequence of RGBA pixels
function asRGBA(data : seq<byte>, desc : Desc) : seq<RGBA>
  requires |data| == desc.width as int * desc.height as int * desc.channels as int
  ensures toByteStream(desc, asRGBA(data, desc)) == data
  ensures |asRGBA(data, desc)| == desc.width as int * desc.height as int
{
  if desc.channels == 3 then
    asRGBA3(data)
  else 
    asRGBA4(data)
}

// Metoda principală de CODIFICARE a unei imagini complete
method encodeAll(image : Image) returns (r : seq<byte>)
  requires validImage(image)
  ensures validByteStream(r)
{
  var header := genHeader(image.desc);
  var footer := genFooter();

  // 1. Convertim datele raw în pixeli structurați
  var rgbs := asRGBA(image.data, image.desc);

  // 2. Codificăm pixelii (rezultă un lanț inversat pentru viteză)
  var opsReversed := encodeAEI(rgbs);

  // 3. Inversăm lanțul pentru ordinea corectă
  var ops := ReverseOpChain(opsReversed);

  // 4. Transformăm operațiunile în bucăți de bytes
  var bitsChainReversed := encodeBitSeq_Chain(ops);
  
  // 5. Aplatizăm bucățile într-un singur array
  var bits := FlattenBytesIterative(bitsChainReversed);

  // Construim fișierul final: Header + Data + Footer (7 zero-uri și un 1)
  r := header + bits + footer;
}

// Extract image metadata from header
method parseHeader(header : seq<byte>) returns (r : Option<Desc>)
  requires |header| == 14
  ensures validHeader(header) ==> r.Some? && r.some == specHeader(header)
  ensures !validHeader(header) ==> r.None?
{
  if header[0..4] != [ 'q' as byte, 'o' as byte, 'i' as byte, 'f' as byte ] {
    return None;
  }
  if 3 <= header[12] <= 4 && validColorSpaceAsByte(header[13]) {
    var desc := Desc(
    pack(header[4..8]),
    pack(header[8..12]),
    header[12] as Channels,
    colorSpaceFromByte(header[13]));
    pack_unpack(header[4..8]);
    pack_unpack(header[8..12]);
    assert genHeader(desc) == header;
    assert validHeader(header);
    return Some(desc);
  }
  return None;
}

    
// Helper pentru eliminarea canalului Alpha (Strict imutabil)
method filterAlphaIterative(data: seq<byte>) returns (res: seq<byte>)
  requires |data| % 4 == 0 // Caller-ul TREBUIE sa dea un buffer RGBA valid
  ensures |res| == (|data| / 4) * 3 // Promitem ca rezultatul e exact RGB (fara alpha)
{
  var i := 0;
  var chain := EmptyByte;
  // Invariant critic pentru a demonstra 'ensures' final
  // Spunem ca lungimea datelor acumulate + ce a ramas de procesat se potriveste cu formula
  while i + 4 <= |data| 
    invariant 0 <= i <= |data|
    invariant i % 4 == 0
    invariant ByteChainLength(chain) == (i / 4) * 3
  {
      chain := LinkByte([data[i], data[i+1], data[i+2]], chain);
      i := i + 4;
  }
  res := FlattenBytesIterative(chain);
}

// Metoda principală de DECODIFICARE a unui stream de bytes într-o imagine
method decodeAll(byteStream : seq<byte>) returns (r : Option<Image>)
    // Post-condiție: Dacă reușim (Some), imaginea returnată respectă invariantul de validitate.
  ensures r.Some? ==> validImage(r.some)
{
  // Verificăm lungimea minimă (Header + Footer)
  if (|byteStream| < 14 + 8) {
    return None;
  } 
  else {
    var len := |byteStream|;
    var header := byteStream[..14];
    var footer := byteStream[len - 8..];

    // Verificăm Footer-ul
    if (footer != genFooter()) { return None; }
    
    // Parsează Header-ul
    var descOption := parseHeader(header);
    if (descOption.None?) { return None; }
    var desc := descOption.some;
    
    // 1. Extragem operațiunile din stream
    var ops := decodeBitSeq_Iterative(byteStream[14..len-8]);
    
    // 2. Reconstruim pixelii (folosind Chain pentru a evita copierea memoriei)
    var chain := decodeAEI_PureChain(ops);
    
    // 3. Aplatizăm în buffer RGBA raw
    var rawDataRGBA := FlattenBytesIterative(chain);
    
    // Verificăm dacă dimensiunea datelor corespunde cu lățimea * înălțimea din header
    var expectedSize := desc.width as int * desc.height as int * 4;
    if |rawDataRGBA| != expectedSize {
        return None;
    }

    // 4. Gestionăm canalele (dacă e RGB, scoatem alpha; dacă e RGBA, îl păstrăm)
    var finalData : seq<byte>;
    if desc.channels == 4 {
       finalData := rawDataRGBA;
    } 
    else {
       finalData := filterAlphaIterative(rawDataRGBA);
    }
    
    // Verificare finală de consistență
    if |finalData| != desc.width as int * desc.height as int * desc.channels as int {
        return None;
    }

    return Some(Image(desc, finalData));
  }
}