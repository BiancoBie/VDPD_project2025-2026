// Dafny program entry.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: build --target cs entry.dfy file_input.cs --allow-warnings
// entry.dfy

method Main(_noArgsParameter: seq<seq<char>>)
{
  var input: array<byte> := FileInput.Reader.getContent();
  if input.Length < 8 {
    print ""Invalid input"";
  } else {
    var b := FileInput.Reader.shouldEncode();
    if b {
      print ""Encoding"", ""\n"";
      var width: uint32 := pack(input[0 .. 4]);
      var height: uint32 := pack(input[4 .. 8]);
      var channels: byte := FileInput.Reader.getChannels();
      assert 3 <= channels as int <= 4;
      print ""Width = "", width, ""\n"";
      print ""Height = "", height, ""\n"";
      print ""Channels = "", channels, ""\n"";
      if input.Length as int - 8 != width as int * height as int * channels as int {
        print ""Invalid input (width * height * channels)"";
      } else {
        var image: Image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
        var s: seq<byte> := encodeAll(image);
        var repeat := 0;
        while repeat < 0
          invariant 0 <= repeat <= 0
          decreases 0 - repeat
        {
          input := FileInput.Reader.getContent();
          image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
          s := encodeAll(image);
          repeat := repeat + 1;
        }
        var result: array<byte> := new byte[|s|];
        var i := 0;
        while i < |s|
          invariant 0 <= i <= |s|
          decreases |s| - i
        {
          result[i] := s[i];
          i := i + 1;
        }
        FileInput.Reader.putContent(result);
      }
    } else {
      print ""Decoding"";
      var result: Option<Image> := decodeAll(input[..]);
      var repeat := 0;
      while repeat < 99999
        invariant 0 <= repeat <= 100000
        decreases 99999 - repeat
      {
        var myinput := FileInput.Reader.getContent();
        result := decodeAll(myinput[..]);
        repeat := repeat + 1;
      }
      if result.None? {
        print ""Invalid encoding"";
      } else {
        var image: Image := result.some;
        var w: uint32 := image.desc.width;
        var h: uint32 := image.desc.height;
        var ws := unpack(w);
        var hs := unpack(h);
        var buffer: array<byte> := new byte[8 + |image.data|];
        buffer[0] := ws[0];
        buffer[1] := ws[1];
        buffer[2] := ws[2];
        buffer[3] := ws[3];
        buffer[4] := hs[0];
        buffer[5] := hs[1];
        buffer[6] := hs[2];
        buffer[7] := hs[3];
        var i: int := 0;
        while i < |image.data|
          invariant 0 <= i <= |image.data|
          decreases |image.data| - i
        {
          buffer[8 + i] := image.data[i];
          i := i + 1;
        }
        FileInput.Reader.putContent(buffer);
      }
    }
  }
}

method ReverseOpChain(chain: OpChain) returns (rev: OpChain)
  ensures |OpChainToSeq(rev)| == |OpChainToSeq(chain)|
  decreases chain
{
  rev := EmptyOp;
  var current := chain;
  while current != EmptyOp
    invariant |OpChainToSeq(rev)| + |OpChainToSeq(current)| == |OpChainToSeq(chain)|
    decreases current
  {
    match current {
      case {:split false} LinkOp(op, next) =>
        rev := LinkOp(op, rev);
        current := next;
      case {:split false} EmptyOp() =>
        break;
    }
  }
}

method FlattenBytesIterative(chain: ByteChain) returns (res: seq<byte>)
  ensures |res| == ByteChainLength(chain)
  decreases chain
{
  res := [];
  var current := chain;
  while current != EmptyByte
    invariant |res| + ByteChainLength(current) == ByteChainLength(chain)
    decreases current
  {
    match current {
      case {:split false} LinkByte(d, next) =>
        res := d + res;
        current := next;
      case {:split false} EmptyByte() =>
        break;
    }
  }
}

function canDiff(curr: RGBA, prev: RGBA): Option<RGBDiff>
  ensures forall dr: Diff, dg: Diff, db: Diff {:trigger RGBDiff(dr, dg, db)} :: (canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==> curr.r == add_byte(prev.r, byte_from(dr as int))) && (canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==> curr.g == add_byte(prev.g, byte_from(dg as int))) && (canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==> curr.b == add_byte(prev.b, byte_from(db as int))) && (canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==> curr.a == prev.a)
  decreases curr, prev
{
  var dr: int := curr.r as int - prev.r as int;
  var dg: int := curr.g as int - prev.g as int;
  var db: int := curr.b as int - prev.b as int;
  var da: int := curr.a as int - prev.a as int;
  if -2 <= dr <= 1 && -2 <= dg <= 1 && -2 <= db <= 1 && da == 0 then
    Some(RGBDiff(dr as Diff, dg as Diff, db as Diff))
  else
    None
}

function canLuma(curr: RGBA, prev: RGBA): Option<RGBLuma>
  ensures forall luma: RGBLuma {:trigger luma.db} {:trigger luma.dr} {:trigger luma.dg} {:trigger Some(luma)} :: (canLuma(curr, prev) == Some(luma) ==> curr.r == add_byte(add_byte(prev.r, byte_from(luma.dg as int)), byte_from(luma.dr as int))) && (canLuma(curr, prev) == Some(luma) ==> curr.g == add_byte(prev.g, byte_from(luma.dg as int))) && (canLuma(curr, prev) == Some(luma) ==> curr.b == add_byte(add_byte(prev.b, byte_from(luma.dg as int)), byte_from(luma.db as int))) && (canLuma(curr, prev) == Some(luma) ==> curr.a == prev.a)
  decreases curr, prev
{
  var dr: int := curr.r as int - prev.r as int;
  var dg: int := curr.g as int - prev.g as int;
  var db: int := curr.b as int - prev.b as int;
  var da: int := curr.a as int - prev.a as int;
  if -32 <= dg <= 31 && -8 <= dr - dg <= 7 && -8 <= db - dg <= 7 && da == 0 then
    assert curr.a == prev.a;
    assert curr.g == add_byte(prev.g, byte_from(dg as Diff64 as int));
    assert curr.r == add_byte(add_byte(prev.r, byte_from(dg as Diff64 as int)), byte_from((dr - dg) as int));
    assert curr.b == add_byte(add_byte(prev.b, byte_from(dg as Diff64 as int)), byte_from((db - dg) as int));
    Some(RGBLuma((dr - dg) as Diff16, dg as Diff64, (db - dg) as Diff16))
  else
    None
}

method encodeAEI(image: seq<RGBA>) returns (chain: OpChain)
  decreases image
{
  chain := EmptyOp;
  var prev: RGBA := RGBA(r := 0, g := 0, b := 0, a := 255);
  var index: array<RGBA> := new RGBA[64] ((i: nat) => RGBA(r := 0, g := 0, b := 0, a := 255));
  var i: int := 0;
  var wh: int := |image|;
  var run := 0;
  while i < wh
    invariant 0 <= i <= wh
    invariant 0 <= run <= 62
    decreases wh - i
  {
    var curr := image[i];
    if curr == prev {
      run := run + 1;
      if run == 62 {
        chain := LinkOp(OpRun(62), chain);
        run := 0;
      }
    } else {
      if run > 0 {
        chain := LinkOp(OpRun(run as Size), chain);
        run := 0;
      }
      var h := hashRGBA(curr);
      if index[h] == curr {
        chain := LinkOp(OpIndex(h as Index64), chain);
      } else {
        index[h] := curr;
        if canDiff(curr, prev).Some? {
          chain := LinkOp(OpDiff(canDiff(curr, prev).some), chain);
        } else if canLuma(curr, prev).Some? {
          chain := LinkOp(OpLuma(canLuma(curr, prev).some), chain);
        } else if curr.a == prev.a {
          chain := LinkOp(OpRGB(RGB(curr.r, curr.g, curr.b)), chain);
        } else {
          chain := LinkOp(OpRGBA(curr), chain);
        }
      }
    }
    prev := curr;
    i := i + 1;
  }
  if run > 0 {
    chain := LinkOp(OpRun(run as Size), chain);
  }
}

method encodeBitSeq_Chain(ops: OpChain) returns (bytes: ByteChain)
  ensures bytes.LinkByte? || bytes.EmptyByte?
  decreases ops
{
  bytes := EmptyByte;
  var current := ops;
  while current != EmptyOp
    decreases current
  {
    match current {
      case {:split false} LinkOp(op, next) =>
        var chunk := encodeBits(op);
        bytes := LinkByte(chunk, bytes);
        current := next;
      case {:split false} EmptyOp() =>
        break;
    }
  }
}

method decodeBitSeq_Iterative(bits: seq<byte>) returns (ops: seq<Op>)
  decreases bits
{
  ops := [];
  var i := 0;
  var len := |bits|;
  while i < len
    invariant 0 <= i <= len
    decreases len - i
  {
    var b1 := bits[i];
    if b1 == 254 {
      if i + 4 <= len {
        ops := ops + [OpRGB(RGB(bits[i + 1], bits[i + 2], bits[i + 3]))];
        i := i + 4;
      } else {
        break;
      }
    } else if b1 == 255 {
      if i + 5 <= len {
        ops := ops + [OpRGBA(RGBA(bits[i + 1], bits[i + 2], bits[i + 3], bits[i + 4]))];
        i := i + 5;
      } else {
        break;
      }
    } else {
      var tag := b1 / 64;
      if tag == 0 {
        ops := ops + [OpIndex(b1 as Index64)];
        i := i + 1;
      } else if tag == 1 {
        var dr := ((b1 / 16 % 4) as int - 2) as Diff;
        var dg := ((b1 / 4 % 4) as int - 2) as Diff;
        var db := ((b1 % 4) as int - 2) as Diff;
        ops := ops + [OpDiff(RGBDiff(dr, dg, db))];
        i := i + 1;
      } else if tag == 2 {
        if i + 2 <= len {
          var b2 := bits[i + 1];
          var dg := ((b1 % 64) as int - 32) as Diff64;
          var dr_dg := ((b2 / 16 % 16) as int - 8) as Diff16;
          var db_dg := ((b2 % 16) as int - 8) as Diff16;
          ops := ops + [OpLuma(RGBLuma(dr_dg, dg, db_dg))];
          i := i + 2;
        } else {
          break;
        }
      } else {
        var run := ((b1 % 64) as int + 1) as Size;
        ops := ops + [OpRun(run)];
        i := i + 1;
      }
    }
  }
}

method decodeAEI_PureChain(ops: seq<Op>) returns (chain: ByteChain)
  decreases ops
{
  chain := EmptyByte;
  var index: seq<RGBA> := seq(64, (i: int) => RGBA(0, 0, 0, 0));
  var prev := RGBA(0, 0, 0, 255);
  var i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |index| == 64
    decreases |ops| - i
  {
    var op := ops[i];
    match op {
      case {:split false} OpRGB(rgb) =>
        prev := RGBA(rgb.r, rgb.g, rgb.b, prev.a);
        chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
        index := index[hashRGBA(prev) := prev];
      case {:split false} OpRGBA(rgba) =>
        prev := rgba;
        chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
        index := index[hashRGBA(prev) := prev];
      case {:split false} OpIndex(idx) =>
        prev := index[idx];
        chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
      case {:split false} OpRun(len) =>
        var chunk := [prev.r, prev.g, prev.b, prev.a];
        var k := 0;
        while k < len as int
          decreases len as int - k
        {
          chain := LinkByte(chunk, chain);
          k := k + 1;
        }
      case {:split false} OpDiff(diff) =>
        prev := RGBA(add_byte(prev.r, byte_from(diff.dr as int)), add_byte(prev.g, byte_from(diff.dg as int)), add_byte(prev.b, byte_from(diff.db as int)), prev.a);
        chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
        index := index[hashRGBA(prev) := prev];
      case {:split false} OpLuma(luma) =>
        var dg := luma.dg as int;
        var dr := luma.dr as int + dg;
        var db := luma.db as int + dg;
        prev := RGBA(add_byte(prev.r, byte_from(dr)), add_byte(prev.g, byte_from(dg)), add_byte(prev.b, byte_from(db)), prev.a);
        chain := LinkByte([prev.r, prev.g, prev.b, prev.a], chain);
        index := index[hashRGBA(prev) := prev];
    }
    i := i + 1;
  }
}

function asRGBA3(data: seq<byte>): seq<RGBA>
  requires |data| % 3 == 0
  ensures toByteStreamRGB(asRGBA3(data)) == data
  ensures |asRGBA3(data)| == |data| / 3
  decreases data
{
  if |data| == 0 then
    []
  else
    [RGBA(data[0], data[1], data[2], 255)] + asRGBA3(data[3..])
}

function asRGBA4(data: seq<byte>): seq<RGBA>
  requires |data| % 4 == 0
  ensures toByteStreamRGBA(asRGBA4(data)) == data
  ensures |asRGBA4(data)| == |data| / 4
  decreases data
{
  if |data| == 0 then
    []
  else
    [RGBA(data[0], data[1], data[2], data[3])] + asRGBA4(data[4..])
}

function asRGBA(data: seq<byte>, desc: Desc): seq<RGBA>
  requires |data| == desc.width as int * desc.height as int * desc.channels as int
  ensures toByteStream(desc, asRGBA(data, desc)) == data
  ensures |asRGBA(data, desc)| == desc.width as int * desc.height as int
  decreases data, desc
{
  if desc.channels == 3 then
    asRGBA3(data)
  else
    asRGBA4(data)
}

method encodeAll(image: Image) returns (r: seq<byte>)
  requires validImage(image)
  ensures validByteStream(r)
  decreases image
{
  var header := genHeader(image.desc);
  var footer := genFooter();
  var rgbs := asRGBA(image.data, image.desc);
  var opsReversed := encodeAEI(rgbs);
  var ops := ReverseOpChain(opsReversed);
  var bitsChainReversed := encodeBitSeq_Chain(ops);
  var bits := FlattenBytesIterative(bitsChainReversed);
  r := header + bits + footer;
}

method parseHeader(header: seq<byte>) returns (r: Option<Desc>)
  requires |header| == 14
  ensures validHeader(header) ==> r.Some? && r.some == specHeader(header)
  ensures !validHeader(header) ==> r.None?
  decreases header
{
  if header[0 .. 4] != ['q' as byte, 'o' as byte, 'i' as byte, 'f' as byte] {
    return None;
  }
  if 3 <= header[12] <= 4 && validColorSpaceAsByte(header[13]) {
    var desc := Desc(pack(header[4 .. 8]), pack(header[8 .. 12]), header[12] as Channels, colorSpaceFromByte(header[13]));
    pack_unpack(header[4 .. 8]);
    pack_unpack(header[8 .. 12]);
    assert genHeader(desc) == header;
    assert validHeader(header);
    return Some(desc);
  }
  return None;
}

method filterAlphaIterative(data: seq<byte>) returns (res: seq<byte>)
  requires |data| % 4 == 0
  ensures |res| == |data| / 4 * 3
  decreases data
{
  var i := 0;
  var chain := EmptyByte;
  while i + 4 <= |data|
    invariant 0 <= i <= |data|
    invariant i % 4 == 0
    invariant ByteChainLength(chain) == i / 4 * 3
    decreases |data| - (i + 4)
  {
    chain := LinkByte([data[i], data[i + 1], data[i + 2]], chain);
    i := i + 4;
  }
  res := FlattenBytesIterative(chain);
}

method decodeAll(byteStream: seq<byte>) returns (r: Option<Image>)
  ensures r.Some? ==> validImage(r.some)
  decreases byteStream
{
  if |byteStream| < 14 + 8 {
    return None;
  } else {
    var len := |byteStream|;
    var header := byteStream[..14];
    var footer := byteStream[len - 8..];
    if footer != genFooter() {
      return None;
    }
    var descOption := parseHeader(header);
    if descOption.None? {
      return None;
    }
    var desc := descOption.some;
    var ops := decodeBitSeq_Iterative(byteStream[14 .. len - 8]);
    var chain := decodeAEI_PureChain(ops);
    var rawDataRGBA := FlattenBytesIterative(chain);
    var expectedSize := desc.width as int * desc.height as int * 4;
    if |rawDataRGBA| != expectedSize {
      return None;
    }
    var finalData: seq<byte>;
    if desc.channels == 4 {
      finalData := rawDataRGBA;
    } else {
      finalData := filterAlphaIterative(rawDataRGBA);
    }
    if |finalData| != desc.width as int * desc.height as int * desc.channels as int {
      return None;
    }
    return Some(Image(desc, finalData));
  }
}

function encodeDiff64(diff: Diff64): byte
  ensures 0 <= encodeDiff64(diff) <= 63
  decreases diff
{
  (diff as int + 32) as byte
}

function encodeDiff16(diff: Diff16): byte
  ensures 0 <= encodeDiff16(diff) <= 15
  decreases diff
{
  (diff as int + 8) as byte
}

function encodeDiff(diff: Diff): byte
  ensures 0 <= encodeDiff(diff) <= 3
  decreases diff
{
  (diff as int + 2) as byte
}

function encodeBits(op: Op): seq<byte>
  ensures validBits(encodeBits(op))
  ensures sizeBitEncoding(opTypeOfOp(op)) == |encodeBits(op)|
  ensures decodeBits(encodeBits(op)) == op
  decreases op
{
  match op {
    case OpRun(size) =>
      [128 + 64 + (size as int - 1) as byte]
    case OpIndex(index) =>
      [index as byte]
    case OpDiff(diff) =>
      [64 + 16 * encodeDiff(diff.dr) + 4 * encodeDiff(diff.dg) + encodeDiff(diff.db)]
    case OpLuma(luma) =>
      [128 + encodeDiff64(luma.dg), 16 * encodeDiff16(luma.dr) + encodeDiff16(luma.db)]
    case OpRGB(rgb) =>
      [254, rgb.r, rgb.g, rgb.b]
    case OpRGBA(rgba) =>
      [255, rgba.r, rgba.g, rgba.b, rgba.a]
  }
}

function opTypeOfBits(bits: byte): OpType
  decreases bits
{
  if bits == 254 then
    TypeRGB
  else if bits == 255 then
    TypeRGBA
  else if bits >= 128 + 64 then
    TypeRun
  else if bits >= 128 then
    TypeLuma
  else if bits >= 64 then
    TypeDiff
  else
    TypeIndex
}

function opTypeOfOp(op: Op): OpType
  decreases op
{
  match op {
    case OpRun(size: Size) =>
      TypeRun
    case OpIndex(index: Index64) =>
      TypeIndex
    case OpDiff(diff: RGBDiff) =>
      TypeDiff
    case OpLuma(luma: RGBLuma) =>
      TypeLuma
    case OpRGB(rgb: RGB) =>
      TypeRGB
    case OpRGBA(rgba: RGBA) =>
      TypeRGBA
  }
}

lemma opTypeOfBits_correct(op: Op)
  ensures opTypeOfOp(op) == opTypeOfBits(encodeBits(op)[0])
  decreases op
{
}

function sizeBitEncoding(opType: OpType): int
  decreases opType
{
  match opType {
    case TypeRun() =>
      1
    case TypeIndex() =>
      1
    case TypeDiff() =>
      1
    case TypeLuma() =>
      2
    case TypeRGB() =>
      4
    case TypeRGBA() =>
      5
  }
}

function validBits(bits: seq<byte>): bool
  decreases bits
{
  |bits| > 0 &&
  match opTypeOfBits(bits[0]) { case TypeRun() => |bits| == 1 && bits[0] >= 128 + 64 && bits[0] - 128 - 64 <= 61 case TypeLuma() => |bits| == 2 && bits[0] >= 128 && bits[0] < 128 + 64 case TypeDiff() => |bits| == 1 && bits[0] >= 64 && bits[0] < 128 case TypeIndex() => |bits| == 1 && bits[0] < 64 case TypeRGBA() => |bits| == 5 && bits[0] == 255 case TypeRGB() => |bits| == 4 && bits[0] == 254 }
}

function decodeBits(bits: seq<byte>): Op
  requires validBits(bits)
  decreases bits
{
  match opTypeOfBits(bits[0]) {
    case TypeRun() =>
      assert |bits| == 1 && bits[0] >= 128 + 64 && bits[0] - 128 - 64 <= 61; OpRun((bits[0] - 128 - 64 + 1) as Size)
    case TypeLuma() =>
      OpLuma(RGBLuma(((bits[1] / 16) as int - 8) as Diff16, ((bits[0] - 128) as int - 32) as Diff64, ((bits[1] % 16) as int - 8) as Diff16))
    case TypeDiff() =>
      assert bits[0] < 128; OpDiff(RGBDiff((((bits[0] - 64) / 16) as int - 2) as Diff, ((bits[0] / 4 % 4) as int - 2) as Diff, ((bits[0] % 4) as int - 2) as Diff))
    case TypeIndex() =>
      OpIndex(bits[0] as Index64)
    case TypeRGBA() =>
      OpRGBA(RGBA(bits[1], bits[2], bits[3], bits[4]))
    case TypeRGB() =>
      OpRGB(RGB(bits[1], bits[2], bits[3]))
  }
}

predicate validBitSeq(bits: seq<byte>)
  decreases bits
{
  |bits| == 0 || var len: int := sizeBitEncoding(opTypeOfBits(bits[0])); |bits| >= len && validBits(bits[0 .. len]) && validBitSeq(bits[len..])
}

function encodeBitSeq(ops: seq<Op>): seq<byte>
  ensures validBitSeq(encodeBitSeq(ops))
  ensures decodeBitSeqSure(encodeBitSeq(ops)) == ops
  decreases ops
{
  if |ops| == 0 then
    []
  else
    encodeBits(ops[0]) + encodeBitSeq(ops[1..])
}

function decodeBitSeqSure(bits: seq<byte>): seq<Op>
  requires validBitSeq(bits)
  decreases bits
{
  if |bits| == 0 then
    []
  else
    var len: int := sizeBitEncoding(opTypeOfBits(bits[0])); [decodeBits(bits[0 .. len])] + decodeBitSeqSure(bits[len..])
}

method decodeBitSeq(bits: seq<byte>) returns (r: Option<seq<Op>>)
  ensures !validBitSeq(bits) ==> r.None?
  ensures validBitSeq(bits) ==> r.Some? && r.some == decodeBitSeqSure(bits)
  decreases bits
{
  if |bits| == 0 {
    r := Some([]);
  } else {
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    if |bits| < len {
      return None;
    } else {
      if validBits(bits[0 .. len]) {
        var rec := decodeBitSeq(bits[len..]);
        if rec.None? {
          return None;
        } else {
          r := Some([decodeBits(bits[0 .. len])] + rec.some);
        }
      } else {
        return None;
      }
    }
  }
}

function genHeader(desc: Desc): seq<byte>
  ensures validHeader(genHeader(desc))
  ensures specHeader(genHeader(desc)) == desc
  decreases desc
{
  ['q' as byte, 'o' as byte, 'i' as byte, 'f' as byte] + unpack(desc.width) + unpack(desc.height) + [desc.channels as byte] + [byteFromColorSpace(desc.colorSpace)]
}

predicate validHeader(bits: seq<byte>)
  decreases bits
{
  |bits| == 14 &&
  bits[0 .. 4] == ['q' as byte, 'o' as byte, 'i' as byte, 'f' as byte] &&
  3 <= bits[12] <= 4 &&
  0 <= bits[13] <= 1
}

function specHeader(header: seq<byte>): Desc
  requires validHeader(header)
  decreases header
{
  Desc(pack(header[4 .. 8]), pack(header[8 .. 12]), header[12] as Channels, colorSpaceFromByte(header[13]))
}

function genFooter(): seq<byte>
{
  seq(7, (i: int) => 0 as byte) + [1 as byte]
}

predicate validFooter(bits: seq<byte>)
  decreases bits
{
  bits == genFooter()
}

predicate validByteStream(byteStream: seq<byte>)
  decreases byteStream
{
  var len: int := |byteStream|;
  |byteStream| >= 14 + 8 &&
  validHeader(byteStream[..14]) &&
  validFooter(byteStream[len - 8..]) &&
  validBitSeq(byteStream[14 .. len - 8]) &&
  |specOps(decodeBitSeqSure(byteStream[14 .. len - 8]))| == specHeader(byteStream[..14]).width as int * specHeader(byteStream[..14]).height as int
}

function specEndToEnd(byteStream: seq<byte>): Image
  requires validByteStream(byteStream)
  decreases byteStream
{
  var desc: Desc := specHeader(byteStream[..14]);
  var len: int := |byteStream|;
  Image(desc, toByteStream(desc, specOps(decodeBitSeqSure(byteStream[14 .. len - 8]))))
}

function byteFromColorSpace(colorSpace: ColorSpace): byte
  decreases colorSpace
{
  match colorSpace {
    case SRGB() =>
      0
    case Linear() =>
      1
  }
}

predicate validColorSpaceAsByte(b: byte)
  decreases b
{
  b == 0 || b == 1
}

function colorSpaceFromByte(b: byte): ColorSpace
  requires validColorSpaceAsByte(b)
  decreases b
{
  if b == 0 then
    SRGB
  else
    Linear
}

function hashRGBA(color: RGBA): byte
  ensures 0 <= hashRGBA(color) <= 63
  decreases color
{
  ((color.r as int * 3 + color.g as int * 5 + color.b as int * 7 + color.a as int * 11) % 64) as byte
}

function hash(color: RGB): byte
  ensures 0 <= hash(color) <= 63
  decreases color
{
  hashRGBA(RGBA(color.r, color.g, color.b, 255))
}

predicate validImage(image: Image)
  decreases image
{
  |image.data| == image.desc.width as int * image.desc.height as int * image.desc.channels as int
}

ghost predicate validState(state: State)
  decreases state
{
  |state.index| == 64
}

function updateState(previous: State, pixel: RGBA): State
  requires validState(previous)
  ensures validState(updateState(previous, pixel))
  decreases previous, pixel
{
  State(prev := pixel, index := previous.index[hashRGBA(pixel) := pixel])
}

function initState(): State
{
  State(prev := RGBA(0, 0, 0, 255), index := seq(64, (i: int) => RGBA(r := 0, g := 0, b := 0, a := 255)))
}

function updateStateStar(previous: State, pixels: seq<RGBA>): State
  requires validState(previous)
  ensures validState(updateStateStar(previous, pixels))
  decreases previous, pixels
{
  if |pixels| == 0 then
    previous
  else
    updateState(updateStateStar(previous, pixels[..|pixels| - 1]), pixels[|pixels| - 1])
}

lemma /*{:_inductionTrigger updateStateStar(state, pixels1 + pixels2), updateStateStar(state1, pixels2)}*/ /*{:_inductionTrigger pixels1 + pixels2, validState(state1), validState(state)}*/ /*{:_induction state, pixels1, state1, pixels2}*/ updateStateStarConcat(state: State, pixels1: seq<RGBA>, state1: State, pixels2: seq<RGBA>, state2: State)
  requires validState(state)
  requires validState(state1)
  requires validState(state2)
  requires updateStateStar(state, pixels1) == state1
  requires updateStateStar(state1, pixels2) == state2
  ensures updateStateStar(state, pixels1 + pixels2) == state2
  decreases |pixels2|
{
  if |pixels2| == 0 {
    assert pixels1 + pixels2 == pixels1;
  } else {
    ghost var len := |pixels2|;
    ghost var state2p := updateStateStar(state1, pixels2[..len - 1]);
    updateStateStarConcat(state, pixels1, state1, pixels2[..len - 1], state2p);
    assert pixels1 + pixels2 == pixels1 + pixels2[..len - 1] + [pixels2[len - 1]];
  }
}

function specDecodeOp(state: State, op: Op): seq<RGBA>
  requires validState(state)
  decreases state, op
{
  match op {
    case OpRGB(RGB(r, g, b)) =>
      [RGBA(r, g, b, state.prev.a)]
    case OpRun(size) =>
      seq(size, (i: int) => state.prev)
    case OpIndex(index) =>
      [state.index[index]]
    case OpDiff(RGBDiff(dr, dg, db)) =>
      [RGBA(add_byte(state.prev.r, byte_from(dr as int)), add_byte(state.prev.g, byte_from(dg as int)), add_byte(state.prev.b, byte_from(db as int)), state.prev.a)]
    case OpLuma(RGBLuma(dr, dg, db)) =>
      [RGBA(add_byte(add_byte(state.prev.r, byte_from(dg as int)), byte_from(dr as int)), add_byte(state.prev.g, byte_from(dg as int)), add_byte(add_byte(state.prev.b, byte_from(dg as int)), byte_from(db as int)), state.prev.a)]
    case OpRGBA(rgba) =>
      [rgba]
  }
}

function specOpsAux(ops: seq<Op>, state: State): seq<RGBA>
  requires validState(state)
  decreases ops, state
{
  if |ops| == 0 then
    []
  else
    var pixels: seq<RGBA> := specDecodeOp(state, ops[0]); pixels + specOpsAux(ops[1..], updateStateStar(state, pixels))
}

lemma /*{:_inductionTrigger |ops|, validState(state)}*/ /*{:_induction ops, state}*/ specOpsAuxAssoc(ops: seq<Op>, state: State)
  requires validState(state)
  requires |ops| > 0
  ensures specOpsAux(ops[..|ops| - 1], state) + specDecodeOp(updateStateStar(state, specOpsAux(ops[..|ops| - 1], state)), ops[|ops| - 1]) == specOpsAux(ops, state)
  decreases ops, state
{
  if |ops| - 1 == 0 {
  } else {
    ghost var len := |ops|;
    ghost var ops1 := ops[1..];
    assert |ops1| == len - 1;
    ghost var len1 := |ops1|;
    ghost var state1 := updateStateStar(state, specDecodeOp(state, ops[0]));
    specOpsAuxAssoc(ops1, state1);
    assert specOpsAux(ops1[..len1 - 1], state1) + specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]) == specOpsAux(ops1, state1);
    ghost var pixels1 := specDecodeOp(state, ops[0]);
    assert specOpsAux(ops, state) == pixels1 + specOpsAux(ops1, state1);
    assert ops1[|ops1| - 1] == ops[|ops| - 1];
    assert ops1[..|ops1| - 1] == ops[1 .. |ops| - 1];
    assert specOpsAux(ops[..|ops| - 1], state) == pixels1 + specOpsAux(ops1[..len1 - 1], state1);
    assert ops[|ops| - 1] == ops1[len1 - 1];
    updateStateStarConcat(state, pixels1, state1, specOpsAux(ops1[..len1 - 1], state1), updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)));
    assert updateStateStar(state, specOpsAux(ops[..|ops| - 1], state)) == updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1));
    assert specDecodeOp(updateStateStar(state, specOpsAux(ops[..|ops| - 1], state)), ops[|ops| - 1]) == specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]);
    assert specOpsAux(ops, state) == specOpsAux(ops[..|ops| - 1], state) + specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]);
  }
}

function specOps(ops: seq<Op>): seq<RGBA>
  decreases ops
{
  specOpsAux(ops, initState())
}

function toByteStreamRGB(data: seq<RGBA>): seq<byte>
  decreases data
{
  if |data| == 0 then
    []
  else
    [data[0].r, data[0].g, data[0].b] + toByteStreamRGB(data[1..])
}

function toByteStreamRGBA(data: seq<RGBA>): seq<byte>
  decreases data
{
  if |data| == 0 then
    []
  else
    [data[0].r, data[0].g, data[0].b, data[0].a] + toByteStreamRGBA(data[1..])
}

function toByteStream(desc: Desc, data: seq<RGBA>): seq<byte>
  decreases desc, data
{
  match desc.channels {
    case 3 =>
      toByteStreamRGB(data)
    case 4 =>
      toByteStreamRGBA(data)
  }
}

predicate validAEI(aei: AEI)
  decreases aei
{
  |specOps(aei.ops)| == aei.width as int * aei.height as int
}

function spec(aei: AEI): seq<RGBA>
  requires validAEI(aei)
  decreases aei
{
  specOps(aei.ops)
}

function add_byte(x: byte, y: byte): byte
  decreases x, y
{
  ((x as int + y as int) % 256) as byte
}

function sub_byte(x: byte, y: byte): byte
  decreases x, y
{
  ((x as int + 256 - y as int) % 256) as byte
}

lemma add_sub(x: byte, y: byte)
  ensures sub_byte(add_byte(x, y), y) == x
  decreases x, y
{
}

function byte_from(x: int): byte
  decreases x
{
  (x % 256) as byte
}

function unpack(x: uint32): seq<byte>
  ensures |unpack(x)| == 4
  decreases x
{
  var b0: byte := (x / (256 * 256 * 256) % 256) as byte;
  var b1: byte := (x / (256 * 256) % 256) as byte;
  var b2: byte := (x / 256 % 256) as byte;
  var b3: byte := (x % 256) as byte;
  [b0, b1, b2, b3]
}

function pack(x: seq<byte>): uint32
  requires |x| == 4
  decreases x
{
  x[0] as uint32 * 16777216 + x[1] as uint32 * 65536 + x[2] as uint32 * 256 + x[3] as uint32
}

lemma pack_unpack(x: seq<byte>)
  requires |x| == 4
  ensures unpack(pack(x)) == x
  decreases x
{
}

lemma unpack_pack(x: uint32)
  ensures pack(unpack(x)) == x
  decreases x
{
}

ghost function OpChainToSeq(c: OpChain): seq<Op>
  decreases c
{
  match c
  case EmptyOp() =>
    []
  case LinkOp(op, next) =>
    [op] + OpChainToSeq(next)
}

ghost function ByteChainLength(c: ByteChain): int
  decreases c
{
  match c
  case EmptyByte() =>
    0
  case LinkByte(data, next) =>
    |data| + ByteChainLength(next)
}

import opened Byte

datatype OpChain = EmptyOp | LinkOp(op: Op, next: OpChain)

datatype ByteChain = EmptyByte | LinkByte(data: seq<byte>, next: ByteChain)

datatype OpType = TypeRun | TypeIndex | TypeDiff | TypeLuma | TypeRGB | TypeRGBA

datatype RGB = RGB(r: byte, g: byte, b: byte)

datatype RGBA = RGBA(r: byte, g: byte, b: byte, a: byte)

newtype {:nativeType ""byte""} Channels = x: int
  | 3 <= x <= 4
  witness 3

datatype ColorSpace = SRGB | Linear

datatype Desc = Desc(width: uint32, height: uint32, channels: Channels, colorSpace: ColorSpace)

datatype Image = Image(desc: Desc, data: seq<byte>)

newtype {:nativeType ""byte""} Size = x: int
  | 1 <= x <= 62
  witness 1

newtype {:nativeType ""byte""} Index64 = x: int
  | 0 <= x <= 63

newtype {:nativeType ""short""} Diff64 = x: int
  | -32 <= x <= 31

newtype {:nativeType ""short""} Diff16 = x: int
  | -8 <= x <= 7

newtype {:nativeType ""short""} Diff = x: int
  | -2 <= x <= 1

datatype RGBDiff = RGBDiff(dr: Diff, dg: Diff, db: Diff)

datatype RGBLuma = RGBLuma(dr: Diff16, dg: Diff64, db: Diff16)

datatype Op = OpRun(size: Size) | OpIndex(index: Index64) | OpDiff(diff: RGBDiff) | OpLuma(luma: RGBLuma) | OpRGB(rgb: RGB) | OpRGBA(rgba: RGBA)

datatype AEI = AEI(width: uint32, height: uint32, ops: seq<Op>)

datatype State = State(prev: RGBA, index: seq<RGBA>)

datatype Option<T> = None | Some(some: T)

module Byte {
  newtype {:nativeType ""byte""} byte = x: int
    | 0 <= x < 256
}

import opened Byte

newtype {:nativeType ""uint""} uint32 = x: int
  | 0 <= x < 4294967296

module {:extern ""FileInput""} FileInput {

  import opened Byte
  class {:extern ""Reader""} Reader {
    static function {:extern ""shouldEncode""} shouldEncode(): bool

    static function {:extern ""getContent""} getContent(): array<byte>

    static method {:extern ""putContent""} putContent(x: array<byte>)
      decreases x

    static function {:extern ""getTimestamp""} getTimestamp(): int

    static function {:extern ""getChannels""} getChannels(): byte
      ensures 3 <= getChannels() as int <= 4
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
}
// end of class FuncExtensions
namespace Byte {


  public partial class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(byte __source) {
      return true;
    }
  }
} // end of namespace Byte
namespace FileInput {


} // end of namespace FileInput
namespace _module {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      byte[] _0_input;
      _0_input = FileInput.Reader.getContent();
      if ((new BigInteger((_0_input).Length)) < (new BigInteger(8))) {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid input")).ToVerbatimString(false));
      } else {
        bool _1_b;
        _1_b = FileInput.Reader.shouldEncode();
        if (_1_b) {
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Encoding")).ToVerbatimString(false));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
          uint _2_width;
          _2_width = __default.pack(Dafny.Helpers.SeqFromArray(_0_input).Subsequence(BigInteger.Zero, new BigInteger(4)));
          uint _3_height;
          _3_height = __default.pack(Dafny.Helpers.SeqFromArray(_0_input).Subsequence(new BigInteger(4), new BigInteger(8)));
          byte _4_channels;
          _4_channels = FileInput.Reader.getChannels();
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Width = ")).ToVerbatimString(false));
          Dafny.Helpers.Print((_2_width));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Height = ")).ToVerbatimString(false));
          Dafny.Helpers.Print((_3_height));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Channels = ")).ToVerbatimString(false));
          Dafny.Helpers.Print((_4_channels));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
          if (((new BigInteger((_0_input).Length)) - (new BigInteger(8))) != (((new BigInteger(_2_width)) * (new BigInteger(_3_height))) * (new BigInteger(_4_channels)))) {
            Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid input (width * height * channels)")).ToVerbatimString(false));
          } else {
            _IImage _5_image;
            _5_image = _module.Image.create(_module.Desc.create(_2_width, _3_height, (byte)(_4_channels), _module.ColorSpace.create_SRGB()), Dafny.Helpers.SeqFromArray(_0_input).Drop(new BigInteger(8)));
            Dafny.ISequence<byte> _6_s;
            Dafny.ISequence<byte> _out0;
            _out0 = __default.encodeAll(_5_image);
            _6_s = _out0;
            BigInteger _7_repeat;
            _7_repeat = BigInteger.Zero;
            while ((_7_repeat).Sign == -1) {
              _0_input = FileInput.Reader.getContent();
              _5_image = _module.Image.create(_module.Desc.create(_2_width, _3_height, (byte)(_4_channels), _module.ColorSpace.create_SRGB()), Dafny.Helpers.SeqFromArray(_0_input).Drop(new BigInteger(8)));
              Dafny.ISequence<byte> _out1;
              _out1 = __default.encodeAll(_5_image);
              _6_s = _out1;
              _7_repeat = (_7_repeat) + (BigInteger.One);
            }
            byte[] _8_result;
            byte[] _nw0 = new byte[Dafny.Helpers.ToIntChecked(new BigInteger((_6_s).Count), "array size exceeds memory limit")];
            _8_result = _nw0;
            BigInteger _9_i;
            _9_i = BigInteger.Zero;
            while ((_9_i) < (new BigInteger((_6_s).Count))) {
              (_8_result)[(int)((_9_i))] = (_6_s).Select(_9_i);
              _9_i = (_9_i) + (BigInteger.One);
            }
            FileInput.Reader.putContent(_8_result);
          }
        } else {
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Decoding")).ToVerbatimString(false));
          _IOption<_IImage> _10_result;
          _IOption<_IImage> _out2;
          _out2 = __default.decodeAll(Dafny.Helpers.SeqFromArray(_0_input));
          _10_result = _out2;
          BigInteger _11_repeat;
          _11_repeat = BigInteger.Zero;
          while ((_11_repeat) < (new BigInteger(99999))) {
            byte[] _12_myinput;
            _12_myinput = FileInput.Reader.getContent();
            _IOption<_IImage> _out3;
            _out3 = __default.decodeAll(Dafny.Helpers.SeqFromArray(_12_myinput));
            _10_result = _out3;
            _11_repeat = (_11_repeat) + (BigInteger.One);
          }
          if ((_10_result).is_None) {
            Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid encoding")).ToVerbatimString(false));
          } else {
            _IImage _13_image;
            _13_image = (_10_result).dtor_some;
            uint _14_w;
            _14_w = ((_13_image).dtor_desc).dtor_width;
            uint _15_h;
            _15_h = ((_13_image).dtor_desc).dtor_height;
            Dafny.ISequence<byte> _16_ws;
            _16_ws = __default.unpack(_14_w);
            Dafny.ISequence<byte> _17_hs;
            _17_hs = __default.unpack(_15_h);
            byte[] _18_buffer;
            byte[] _nw1 = new byte[Dafny.Helpers.ToIntChecked((new BigInteger(8)) + (new BigInteger(((_13_image).dtor_data).Count)), "array size exceeds memory limit")];
            _18_buffer = _nw1;
            (_18_buffer)[(int)((BigInteger.Zero))] = (_16_ws).Select(BigInteger.Zero);
            (_18_buffer)[(int)((BigInteger.One))] = (_16_ws).Select(BigInteger.One);
            (_18_buffer)[(int)((new BigInteger(2)))] = (_16_ws).Select(new BigInteger(2));
            (_18_buffer)[(int)((new BigInteger(3)))] = (_16_ws).Select(new BigInteger(3));
            (_18_buffer)[(int)((new BigInteger(4)))] = (_17_hs).Select(BigInteger.Zero);
            (_18_buffer)[(int)((new BigInteger(5)))] = (_17_hs).Select(BigInteger.One);
            (_18_buffer)[(int)((new BigInteger(6)))] = (_17_hs).Select(new BigInteger(2));
            (_18_buffer)[(int)((new BigInteger(7)))] = (_17_hs).Select(new BigInteger(3));
            BigInteger _19_i;
            _19_i = BigInteger.Zero;
            while ((_19_i) < (new BigInteger(((_13_image).dtor_data).Count))) {
              BigInteger _index0 = (new BigInteger(8)) + (_19_i);
              (_18_buffer)[(int)(_index0)] = ((_13_image).dtor_data).Select(_19_i);
              _19_i = (_19_i) + (BigInteger.One);
            }
            FileInput.Reader.putContent(_18_buffer);
          }
        }
      }
    }
    public static _IOpChain ReverseOpChain(_IOpChain chain)
    {
      _IOpChain rev = OpChain.Default();
      rev = _module.OpChain.create_EmptyOp();
      _IOpChain _0_current;
      _0_current = chain;
      while (!object.Equals(_0_current, _module.OpChain.create_EmptyOp())) {
        _IOpChain _source0 = _0_current;
        {
          if (_source0.is_LinkOp) {
            _IOp _1_op = _source0.dtor_op;
            _IOpChain _2_next = _source0.dtor_next;
            rev = _module.OpChain.create_LinkOp(_1_op, rev);
            _0_current = _2_next;
            goto after_match0;
          }
        }
        {
          goto after_0;
        }
      after_match0: ;
      continue_0: ;
      }
    after_0: ;
      return rev;
    }
    public static Dafny.ISequence<byte> FlattenBytesIterative(_IByteChain chain)
    {
      Dafny.ISequence<byte> res = Dafny.Sequence<byte>.Empty;
      res = Dafny.Sequence<byte>.FromElements();
      _IByteChain _0_current;
      _0_current = chain;
      while (!object.Equals(_0_current, _module.ByteChain.create_EmptyByte())) {
        _IByteChain _source0 = _0_current;
        {
          if (_source0.is_LinkByte) {
            Dafny.ISequence<byte> _1_d = _source0.dtor_data;
            _IByteChain _2_next = _source0.dtor_next;
            res = Dafny.Sequence<byte>.Concat(_1_d, res);
            _0_current = _2_next;
            goto after_match0;
          }
        }
        {
          goto after_1;
        }
      after_match0: ;
      continue_1: ;
      }
    after_1: ;
      return res;
    }
    public static _IOption<_IRGBDiff> canDiff(_IRGBA curr, _IRGBA prev)
    {
      BigInteger _0_dr = (new BigInteger((curr).dtor_r)) - (new BigInteger((prev).dtor_r));
      BigInteger _1_dg = (new BigInteger((curr).dtor_g)) - (new BigInteger((prev).dtor_g));
      BigInteger _2_db = (new BigInteger((curr).dtor_b)) - (new BigInteger((prev).dtor_b));
      BigInteger _3_da = (new BigInteger((curr).dtor_a)) - (new BigInteger((prev).dtor_a));
      if ((((((new BigInteger(-2)) <= (_0_dr)) && ((_0_dr) <= (BigInteger.One))) && (((new BigInteger(-2)) <= (_1_dg)) && ((_1_dg) <= (BigInteger.One)))) && (((new BigInteger(-2)) <= (_2_db)) && ((_2_db) <= (BigInteger.One)))) && ((_3_da).Sign == 0)) {
        return _module.Option<_IRGBDiff>.create_Some(_module.RGBDiff.create((short)(_0_dr), (short)(_1_dg), (short)(_2_db)));
      } else {
        return _module.Option<_IRGBDiff>.create_None();
      }
    }
    public static _IOption<_IRGBLuma> canLuma(_IRGBA curr, _IRGBA prev)
    {
      BigInteger _0_dr = (new BigInteger((curr).dtor_r)) - (new BigInteger((prev).dtor_r));
      BigInteger _1_dg = (new BigInteger((curr).dtor_g)) - (new BigInteger((prev).dtor_g));
      BigInteger _2_db = (new BigInteger((curr).dtor_b)) - (new BigInteger((prev).dtor_b));
      BigInteger _3_da = (new BigInteger((curr).dtor_a)) - (new BigInteger((prev).dtor_a));
      if ((((((new BigInteger(-32)) <= (_1_dg)) && ((_1_dg) <= (new BigInteger(31)))) && (((new BigInteger(-8)) <= ((_0_dr) - (_1_dg))) && (((_0_dr) - (_1_dg)) <= (new BigInteger(7))))) && (((new BigInteger(-8)) <= ((_2_db) - (_1_dg))) && (((_2_db) - (_1_dg)) <= (new BigInteger(7))))) && ((_3_da).Sign == 0)) {
        return _module.Option<_IRGBLuma>.create_Some(_module.RGBLuma.create((short)((_0_dr) - (_1_dg)), (short)(_1_dg), (short)((_2_db) - (_1_dg))));
      } else {
        return _module.Option<_IRGBLuma>.create_None();
      }
    }
    public static _IOpChain encodeAEI(Dafny.ISequence<_IRGBA> image)
    {
      _IOpChain chain = OpChain.Default();
      chain = _module.OpChain.create_EmptyOp();
      _IRGBA _0_prev;
      _0_prev = _module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(255));
      _IRGBA[] _1_index;
      Func<BigInteger, _IRGBA> _init0 = ((System.Func<BigInteger, _IRGBA>)((_2_i) => {
        return _module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(255));
      }));
      _IRGBA[] _nw0 = new _IRGBA[Dafny.Helpers.ToIntChecked(new BigInteger(64), "array size exceeds memory limit")];
      for (var _i0_0 = 0; _i0_0 < new BigInteger(_nw0.Length); _i0_0++) {
        _nw0[(int)(_i0_0)] = _init0(_i0_0);
      }
      _1_index = _nw0;
      BigInteger _3_i;
      _3_i = BigInteger.Zero;
      BigInteger _4_wh;
      _4_wh = new BigInteger((image).Count);
      BigInteger _5_run;
      _5_run = BigInteger.Zero;
      while ((_3_i) < (_4_wh)) {
        _IRGBA _6_curr;
        _6_curr = (image).Select(_3_i);
        if (object.Equals(_6_curr, _0_prev)) {
          _5_run = (_5_run) + (BigInteger.One);
          if ((_5_run) == (new BigInteger(62))) {
            chain = _module.OpChain.create_LinkOp(_module.Op.create_OpRun((byte)(62)), chain);
            _5_run = BigInteger.Zero;
          }
        } else {
          if ((_5_run).Sign == 1) {
            chain = _module.OpChain.create_LinkOp(_module.Op.create_OpRun((byte)(_5_run)), chain);
            _5_run = BigInteger.Zero;
          }
          byte _7_h;
          _7_h = __default.hashRGBA(_6_curr);
          if (object.Equals((_1_index)[(int)(_7_h)], _6_curr)) {
            chain = _module.OpChain.create_LinkOp(_module.Op.create_OpIndex((byte)(_7_h)), chain);
          } else {
            (_1_index)[(int)((_7_h))] = _6_curr;
            if ((__default.canDiff(_6_curr, _0_prev)).is_Some) {
              chain = _module.OpChain.create_LinkOp(_module.Op.create_OpDiff((__default.canDiff(_6_curr, _0_prev)).dtor_some), chain);
            } else if ((__default.canLuma(_6_curr, _0_prev)).is_Some) {
              chain = _module.OpChain.create_LinkOp(_module.Op.create_OpLuma((__default.canLuma(_6_curr, _0_prev)).dtor_some), chain);
            } else if (((_6_curr).dtor_a) == ((_0_prev).dtor_a)) {
              chain = _module.OpChain.create_LinkOp(_module.Op.create_OpRGB(_module.RGB.create((_6_curr).dtor_r, (_6_curr).dtor_g, (_6_curr).dtor_b)), chain);
            } else {
              chain = _module.OpChain.create_LinkOp(_module.Op.create_OpRGBA(_6_curr), chain);
            }
          }
        }
        _0_prev = _6_curr;
        _3_i = (_3_i) + (BigInteger.One);
      }
      if ((_5_run).Sign == 1) {
        chain = _module.OpChain.create_LinkOp(_module.Op.create_OpRun((byte)(_5_run)), chain);
      }
      return chain;
    }
    public static _IByteChain encodeBitSeq__Chain(_IOpChain ops)
    {
      _IByteChain bytes = ByteChain.Default();
      bytes = _module.ByteChain.create_EmptyByte();
      _IOpChain _0_current;
      _0_current = ops;
      while (!object.Equals(_0_current, _module.OpChain.create_EmptyOp())) {
        _IOpChain _source0 = _0_current;
        {
          if (_source0.is_LinkOp) {
            _IOp _1_op = _source0.dtor_op;
            _IOpChain _2_next = _source0.dtor_next;
            Dafny.ISequence<byte> _3_chunk;
            _3_chunk = __default.encodeBits(_1_op);
            bytes = _module.ByteChain.create_LinkByte(_3_chunk, bytes);
            _0_current = _2_next;
            goto after_match0;
          }
        }
        {
          goto after_2;
        }
      after_match0: ;
      continue_2: ;
      }
    after_2: ;
      return bytes;
    }
    public static Dafny.ISequence<_IOp> decodeBitSeq__Iterative(Dafny.ISequence<byte> bits)
    {
      Dafny.ISequence<_IOp> ops = Dafny.Sequence<_IOp>.Empty;
      ops = Dafny.Sequence<_IOp>.FromElements();
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      BigInteger _1_len;
      _1_len = new BigInteger((bits).Count);
      while ((_0_i) < (_1_len)) {
        byte _2_b1;
        _2_b1 = (bits).Select(_0_i);
        if ((_2_b1) == ((byte)(254))) {
          if (((_0_i) + (new BigInteger(4))) <= (_1_len)) {
            ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpRGB(_module.RGB.create((bits).Select((_0_i) + (BigInteger.One)), (bits).Select((_0_i) + (new BigInteger(2))), (bits).Select((_0_i) + (new BigInteger(3)))))));
            _0_i = (_0_i) + (new BigInteger(4));
          } else {
            goto after_3;
          }
        } else if ((_2_b1) == ((byte)(255))) {
          if (((_0_i) + (new BigInteger(5))) <= (_1_len)) {
            ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpRGBA(_module.RGBA.create((bits).Select((_0_i) + (BigInteger.One)), (bits).Select((_0_i) + (new BigInteger(2))), (bits).Select((_0_i) + (new BigInteger(3))), (bits).Select((_0_i) + (new BigInteger(4)))))));
            _0_i = (_0_i) + (new BigInteger(5));
          } else {
            goto after_3;
          }
        } else {
          byte _3_tag;
          _3_tag = (byte)((_2_b1) / ((byte)(64)));
          if ((_3_tag) == ((byte)(0))) {
            ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpIndex((byte)(_2_b1))));
            _0_i = (_0_i) + (BigInteger.One);
          } else if ((_3_tag) == ((byte)(1))) {
            short _4_dr;
            _4_dr = (short)((new BigInteger((byte)(((byte)((_2_b1) / ((byte)(16)))) % ((byte)(4))))) - (new BigInteger(2)));
            short _5_dg;
            _5_dg = (short)((new BigInteger((byte)(((byte)((_2_b1) / ((byte)(4)))) % ((byte)(4))))) - (new BigInteger(2)));
            short _6_db;
            _6_db = (short)((new BigInteger((byte)((_2_b1) % ((byte)(4))))) - (new BigInteger(2)));
            ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpDiff(_module.RGBDiff.create(_4_dr, _5_dg, _6_db))));
            _0_i = (_0_i) + (BigInteger.One);
          } else if ((_3_tag) == ((byte)(2))) {
            if (((_0_i) + (new BigInteger(2))) <= (_1_len)) {
              byte _7_b2;
              _7_b2 = (bits).Select((_0_i) + (BigInteger.One));
              short _8_dg;
              _8_dg = (short)((new BigInteger((byte)((_2_b1) % ((byte)(64))))) - (new BigInteger(32)));
              short _9_dr__dg;
              _9_dr__dg = (short)((new BigInteger((byte)(((byte)((_7_b2) / ((byte)(16)))) % ((byte)(16))))) - (new BigInteger(8)));
              short _10_db__dg;
              _10_db__dg = (short)((new BigInteger((byte)((_7_b2) % ((byte)(16))))) - (new BigInteger(8)));
              ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpLuma(_module.RGBLuma.create(_9_dr__dg, _8_dg, _10_db__dg))));
              _0_i = (_0_i) + (new BigInteger(2));
            } else {
              goto after_3;
            }
          } else {
            byte _11_run;
            _11_run = (byte)((new BigInteger((byte)((_2_b1) % ((byte)(64))))) + (BigInteger.One));
            ops = Dafny.Sequence<_IOp>.Concat(ops, Dafny.Sequence<_IOp>.FromElements(_module.Op.create_OpRun(_11_run)));
            _0_i = (_0_i) + (BigInteger.One);
          }
        }
      continue_3: ;
      }
    after_3: ;
      return ops;
    }
    public static _IByteChain decodeAEI__PureChain(Dafny.ISequence<_IOp> ops)
    {
      _IByteChain chain = ByteChain.Default();
      chain = _module.ByteChain.create_EmptyByte();
      Dafny.ISequence<_IRGBA> _0_index;
      _0_index = ((System.Func<Dafny.ISequence<_IRGBA>>) (() => {
        BigInteger dim0 = new BigInteger(64);
        var arr0 = new _IRGBA[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _1_i = (BigInteger) i0;
          arr0[(int)(_1_i)] = _module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(0));
        }
        return Dafny.Sequence<_IRGBA>.FromArray(arr0);
      }))();
      _IRGBA _2_prev;
      _2_prev = _module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(255));
      BigInteger _3_i;
      _3_i = BigInteger.Zero;
      while ((_3_i) < (new BigInteger((ops).Count))) {
        _IOp _4_op;
        _4_op = (ops).Select(_3_i);
        _IOp _source0 = _4_op;
        {
          if (_source0.is_OpRGB) {
            _IRGB _5_rgb = _source0.dtor_rgb;
            _2_prev = _module.RGBA.create((_5_rgb).dtor_r, (_5_rgb).dtor_g, (_5_rgb).dtor_b, (_2_prev).dtor_a);
            chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a), chain);
            _0_index = Dafny.Sequence<_IRGBA>.Update(_0_index, __default.hashRGBA(_2_prev), _2_prev);
            goto after_match0;
          }
        }
        {
          if (_source0.is_OpRGBA) {
            _IRGBA _6_rgba = _source0.dtor_rgba;
            _2_prev = _6_rgba;
            chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a), chain);
            _0_index = Dafny.Sequence<_IRGBA>.Update(_0_index, __default.hashRGBA(_2_prev), _2_prev);
            goto after_match0;
          }
        }
        {
          if (_source0.is_OpIndex) {
            byte _7_idx = _source0.dtor_index;
            _2_prev = (_0_index).Select(_7_idx);
            chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a), chain);
            goto after_match0;
          }
        }
        {
          if (_source0.is_OpRun) {
            byte _8_len = _source0.dtor_size;
            Dafny.ISequence<byte> _9_chunk;
            _9_chunk = Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a);
            BigInteger _10_k;
            _10_k = BigInteger.Zero;
            while ((_10_k) < (new BigInteger(_8_len))) {
              chain = _module.ByteChain.create_LinkByte(_9_chunk, chain);
              _10_k = (_10_k) + (BigInteger.One);
            }
            goto after_match0;
          }
        }
        {
          if (_source0.is_OpDiff) {
            _IRGBDiff _11_diff = _source0.dtor_diff;
            _2_prev = _module.RGBA.create(__default.add__byte((_2_prev).dtor_r, __default.byte__from(new BigInteger((_11_diff).dtor_dr))), __default.add__byte((_2_prev).dtor_g, __default.byte__from(new BigInteger((_11_diff).dtor_dg))), __default.add__byte((_2_prev).dtor_b, __default.byte__from(new BigInteger((_11_diff).dtor_db))), (_2_prev).dtor_a);
            chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a), chain);
            _0_index = Dafny.Sequence<_IRGBA>.Update(_0_index, __default.hashRGBA(_2_prev), _2_prev);
            goto after_match0;
          }
        }
        {
          _IRGBLuma _12_luma = _source0.dtor_luma;
          BigInteger _13_dg;
          _13_dg = new BigInteger((_12_luma).dtor_dg);
          BigInteger _14_dr;
          _14_dr = (new BigInteger((_12_luma).dtor_dr)) + (_13_dg);
          BigInteger _15_db;
          _15_db = (new BigInteger((_12_luma).dtor_db)) + (_13_dg);
          _2_prev = _module.RGBA.create(__default.add__byte((_2_prev).dtor_r, __default.byte__from(_14_dr)), __default.add__byte((_2_prev).dtor_g, __default.byte__from(_13_dg)), __default.add__byte((_2_prev).dtor_b, __default.byte__from(_15_db)), (_2_prev).dtor_a);
          chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((_2_prev).dtor_r, (_2_prev).dtor_g, (_2_prev).dtor_b, (_2_prev).dtor_a), chain);
          _0_index = Dafny.Sequence<_IRGBA>.Update(_0_index, __default.hashRGBA(_2_prev), _2_prev);
        }
      after_match0: ;
        _3_i = (_3_i) + (BigInteger.One);
      }
      return chain;
    }
    public static Dafny.ISequence<_IRGBA> asRGBA3(Dafny.ISequence<byte> data) {
      Dafny.ISequence<_IRGBA> _0___accumulator = Dafny.Sequence<_IRGBA>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((data).Count)).Sign == 0) {
        return Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, Dafny.Sequence<_IRGBA>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, Dafny.Sequence<_IRGBA>.FromElements(_module.RGBA.create((data).Select(BigInteger.Zero), (data).Select(BigInteger.One), (data).Select(new BigInteger(2)), (byte)(255))));
        Dafny.ISequence<byte> _in0 = (data).Drop(new BigInteger(3));
        data = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<_IRGBA> asRGBA4(Dafny.ISequence<byte> data) {
      Dafny.ISequence<_IRGBA> _0___accumulator = Dafny.Sequence<_IRGBA>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((data).Count)).Sign == 0) {
        return Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, Dafny.Sequence<_IRGBA>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, Dafny.Sequence<_IRGBA>.FromElements(_module.RGBA.create((data).Select(BigInteger.Zero), (data).Select(BigInteger.One), (data).Select(new BigInteger(2)), (data).Select(new BigInteger(3)))));
        Dafny.ISequence<byte> _in0 = (data).Drop(new BigInteger(4));
        data = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<_IRGBA> asRGBA(Dafny.ISequence<byte> data, _IDesc desc)
    {
      if (((desc).dtor_channels) == ((byte)(3))) {
        return __default.asRGBA3(data);
      } else {
        return __default.asRGBA4(data);
      }
    }
    public static Dafny.ISequence<byte> encodeAll(_IImage image)
    {
      Dafny.ISequence<byte> r = Dafny.Sequence<byte>.Empty;
      Dafny.ISequence<byte> _0_header;
      _0_header = __default.genHeader((image).dtor_desc);
      Dafny.ISequence<byte> _1_footer;
      _1_footer = __default.genFooter();
      Dafny.ISequence<_IRGBA> _2_rgbs;
      _2_rgbs = __default.asRGBA((image).dtor_data, (image).dtor_desc);
      _IOpChain _3_opsReversed;
      _IOpChain _out0;
      _out0 = __default.encodeAEI(_2_rgbs);
      _3_opsReversed = _out0;
      _IOpChain _4_ops;
      _IOpChain _out1;
      _out1 = __default.ReverseOpChain(_3_opsReversed);
      _4_ops = _out1;
      _IByteChain _5_bitsChainReversed;
      _IByteChain _out2;
      _out2 = __default.encodeBitSeq__Chain(_4_ops);
      _5_bitsChainReversed = _out2;
      Dafny.ISequence<byte> _6_bits;
      Dafny.ISequence<byte> _out3;
      _out3 = __default.FlattenBytesIterative(_5_bitsChainReversed);
      _6_bits = _out3;
      r = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_0_header, _6_bits), _1_footer);
      return r;
    }
    public static _IOption<_IDesc> parseHeader(Dafny.ISequence<byte> header)
    {
      _IOption<_IDesc> r = Option<_IDesc>.Default();
      if (!((header).Subsequence(BigInteger.Zero, new BigInteger(4))).Equals(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('q')).Value), (byte)((new Dafny.Rune('o')).Value), (byte)((new Dafny.Rune('i')).Value), (byte)((new Dafny.Rune('f')).Value)))) {
        r = _module.Option<_IDesc>.create_None();
        return r;
      }
      if (((((byte)(3)) <= ((header).Select(new BigInteger(12)))) && (((header).Select(new BigInteger(12))) <= ((byte)(4)))) && (__default.validColorSpaceAsByte((header).Select(new BigInteger(13))))) {
        _IDesc _0_desc;
        _0_desc = _module.Desc.create(__default.pack((header).Subsequence(new BigInteger(4), new BigInteger(8))), __default.pack((header).Subsequence(new BigInteger(8), new BigInteger(12))), (byte)((header).Select(new BigInteger(12))), __default.colorSpaceFromByte((header).Select(new BigInteger(13))));
        r = _module.Option<_IDesc>.create_Some(_0_desc);
        return r;
      }
      r = _module.Option<_IDesc>.create_None();
      return r;
      return r;
    }
    public static Dafny.ISequence<byte> filterAlphaIterative(Dafny.ISequence<byte> data)
    {
      Dafny.ISequence<byte> res = Dafny.Sequence<byte>.Empty;
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      _IByteChain _1_chain;
      _1_chain = _module.ByteChain.create_EmptyByte();
      while (((_0_i) + (new BigInteger(4))) <= (new BigInteger((data).Count))) {
        _1_chain = _module.ByteChain.create_LinkByte(Dafny.Sequence<byte>.FromElements((data).Select(_0_i), (data).Select((_0_i) + (BigInteger.One)), (data).Select((_0_i) + (new BigInteger(2)))), _1_chain);
        _0_i = (_0_i) + (new BigInteger(4));
      }
      Dafny.ISequence<byte> _out0;
      _out0 = __default.FlattenBytesIterative(_1_chain);
      res = _out0;
      return res;
    }
    public static _IOption<_IImage> decodeAll(Dafny.ISequence<byte> byteStream)
    {
      _IOption<_IImage> r = Option<_IImage>.Default();
      if ((new BigInteger((byteStream).Count)) < ((new BigInteger(14)) + (new BigInteger(8)))) {
        r = _module.Option<_IImage>.create_None();
        return r;
      } else {
        BigInteger _0_len;
        _0_len = new BigInteger((byteStream).Count);
        Dafny.ISequence<byte> _1_header;
        _1_header = (byteStream).Take(new BigInteger(14));
        Dafny.ISequence<byte> _2_footer;
        _2_footer = (byteStream).Drop((_0_len) - (new BigInteger(8)));
        if (!(_2_footer).Equals(__default.genFooter())) {
          r = _module.Option<_IImage>.create_None();
          return r;
        }
        _IOption<_IDesc> _3_descOption;
        _IOption<_IDesc> _out0;
        _out0 = __default.parseHeader(_1_header);
        _3_descOption = _out0;
        if ((_3_descOption).is_None) {
          r = _module.Option<_IImage>.create_None();
          return r;
        }
        _IDesc _4_desc;
        _4_desc = (_3_descOption).dtor_some;
        Dafny.ISequence<_IOp> _5_ops;
        Dafny.ISequence<_IOp> _out1;
        _out1 = __default.decodeBitSeq__Iterative((byteStream).Subsequence(new BigInteger(14), (_0_len) - (new BigInteger(8))));
        _5_ops = _out1;
        _IByteChain _6_chain;
        _IByteChain _out2;
        _out2 = __default.decodeAEI__PureChain(_5_ops);
        _6_chain = _out2;
        Dafny.ISequence<byte> _7_rawDataRGBA;
        Dafny.ISequence<byte> _out3;
        _out3 = __default.FlattenBytesIterative(_6_chain);
        _7_rawDataRGBA = _out3;
        BigInteger _8_expectedSize;
        _8_expectedSize = ((new BigInteger((_4_desc).dtor_width)) * (new BigInteger((_4_desc).dtor_height))) * (new BigInteger(4));
        if ((new BigInteger((_7_rawDataRGBA).Count)) != (_8_expectedSize)) {
          r = _module.Option<_IImage>.create_None();
          return r;
        }
        Dafny.ISequence<byte> _9_finalData = Dafny.Sequence<byte>.Empty;
        if (((_4_desc).dtor_channels) == ((byte)(4))) {
          _9_finalData = _7_rawDataRGBA;
        } else {
          Dafny.ISequence<byte> _out4;
          _out4 = __default.filterAlphaIterative(_7_rawDataRGBA);
          _9_finalData = _out4;
        }
        if ((new BigInteger((_9_finalData).Count)) != (((new BigInteger((_4_desc).dtor_width)) * (new BigInteger((_4_desc).dtor_height))) * (new BigInteger((_4_desc).dtor_channels)))) {
          r = _module.Option<_IImage>.create_None();
          return r;
        }
        r = _module.Option<_IImage>.create_Some(_module.Image.create(_4_desc, _9_finalData));
        return r;
      }
      return r;
    }
    public static byte encodeDiff64(short diff) {
      return (byte)((new BigInteger(diff)) + (new BigInteger(32)));
    }
    public static byte encodeDiff16(short diff) {
      return (byte)((new BigInteger(diff)) + (new BigInteger(8)));
    }
    public static byte encodeDiff(short diff) {
      return (byte)((new BigInteger(diff)) + (new BigInteger(2)));
    }
    public static Dafny.ISequence<byte> encodeBits(_IOp op) {
      _IOp _source0 = op;
      {
        if (_source0.is_OpRun) {
          byte _0_size = _source0.dtor_size;
          return Dafny.Sequence<byte>.FromElements((byte)(((byte)(((byte)(128)) + ((byte)(64)))) + ((byte)((new BigInteger(_0_size)) - (BigInteger.One)))));
        }
      }
      {
        if (_source0.is_OpIndex) {
          byte _1_index = _source0.dtor_index;
          return Dafny.Sequence<byte>.FromElements((byte)(_1_index));
        }
      }
      {
        if (_source0.is_OpDiff) {
          _IRGBDiff _2_diff = _source0.dtor_diff;
          return Dafny.Sequence<byte>.FromElements((byte)(((byte)(((byte)(((byte)(64)) + ((byte)(((byte)(16)) * (__default.encodeDiff((_2_diff).dtor_dr)))))) + ((byte)(((byte)(4)) * (__default.encodeDiff((_2_diff).dtor_dg)))))) + (__default.encodeDiff((_2_diff).dtor_db))));
        }
      }
      {
        if (_source0.is_OpLuma) {
          _IRGBLuma _3_luma = _source0.dtor_luma;
          return Dafny.Sequence<byte>.FromElements((byte)(((byte)(128)) + (__default.encodeDiff64((_3_luma).dtor_dg))), (byte)(((byte)(((byte)(16)) * (__default.encodeDiff16((_3_luma).dtor_dr)))) + (__default.encodeDiff16((_3_luma).dtor_db))));
        }
      }
      {
        if (_source0.is_OpRGB) {
          _IRGB _4_rgb = _source0.dtor_rgb;
          return Dafny.Sequence<byte>.FromElements((byte)(254), (_4_rgb).dtor_r, (_4_rgb).dtor_g, (_4_rgb).dtor_b);
        }
      }
      {
        _IRGBA _5_rgba = _source0.dtor_rgba;
        return Dafny.Sequence<byte>.FromElements((byte)(255), (_5_rgba).dtor_r, (_5_rgba).dtor_g, (_5_rgba).dtor_b, (_5_rgba).dtor_a);
      }
    }
    public static _IOpType opTypeOfBits(byte bits) {
      if ((bits) == ((byte)(254))) {
        return _module.OpType.create_TypeRGB();
      } else if ((bits) == ((byte)(255))) {
        return _module.OpType.create_TypeRGBA();
      } else if ((bits) >= ((byte)(((byte)(128)) + ((byte)(64))))) {
        return _module.OpType.create_TypeRun();
      } else if ((bits) >= ((byte)(128))) {
        return _module.OpType.create_TypeLuma();
      } else if ((bits) >= ((byte)(64))) {
        return _module.OpType.create_TypeDiff();
      } else {
        return _module.OpType.create_TypeIndex();
      }
    }
    public static _IOpType opTypeOfOp(_IOp op) {
      _IOp _source0 = op;
      {
        if (_source0.is_OpRun) {
          byte _0_size = _source0.dtor_size;
          return _module.OpType.create_TypeRun();
        }
      }
      {
        if (_source0.is_OpIndex) {
          byte _1_index = _source0.dtor_index;
          return _module.OpType.create_TypeIndex();
        }
      }
      {
        if (_source0.is_OpDiff) {
          _IRGBDiff _2_diff = _source0.dtor_diff;
          return _module.OpType.create_TypeDiff();
        }
      }
      {
        if (_source0.is_OpLuma) {
          _IRGBLuma _3_luma = _source0.dtor_luma;
          return _module.OpType.create_TypeLuma();
        }
      }
      {
        if (_source0.is_OpRGB) {
          _IRGB _4_rgb = _source0.dtor_rgb;
          return _module.OpType.create_TypeRGB();
        }
      }
      {
        _IRGBA _5_rgba = _source0.dtor_rgba;
        return _module.OpType.create_TypeRGBA();
      }
    }
    public static BigInteger sizeBitEncoding(_IOpType opType) {
      _IOpType _source0 = opType;
      {
        if (_source0.is_TypeRun) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_TypeIndex) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_TypeDiff) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_TypeLuma) {
          return new BigInteger(2);
        }
      }
      {
        if (_source0.is_TypeRGB) {
          return new BigInteger(4);
        }
      }
      {
        return new BigInteger(5);
      }
    }
    public static bool validBits(Dafny.ISequence<byte> bits) {
      return ((new BigInteger((bits).Count)).Sign == 1) && (((System.Func<bool>)(() => {
        _IOpType _source0 = __default.opTypeOfBits((bits).Select(BigInteger.Zero));
        {
          if (_source0.is_TypeRun) {
            return (((new BigInteger((bits).Count)) == (BigInteger.One)) && (((bits).Select(BigInteger.Zero)) >= ((byte)(((byte)(128)) + ((byte)(64)))))) && (((byte)(((byte)(((bits).Select(BigInteger.Zero)) - ((byte)(128)))) - ((byte)(64)))) <= ((byte)(61)));
          }
        }
        {
          if (_source0.is_TypeLuma) {
            return (((new BigInteger((bits).Count)) == (new BigInteger(2))) && (((bits).Select(BigInteger.Zero)) >= ((byte)(128)))) && (((bits).Select(BigInteger.Zero)) < ((byte)(((byte)(128)) + ((byte)(64)))));
          }
        }
        {
          if (_source0.is_TypeDiff) {
            return (((new BigInteger((bits).Count)) == (BigInteger.One)) && (((bits).Select(BigInteger.Zero)) >= ((byte)(64)))) && (((bits).Select(BigInteger.Zero)) < ((byte)(128)));
          }
        }
        {
          if (_source0.is_TypeIndex) {
            return ((new BigInteger((bits).Count)) == (BigInteger.One)) && (((bits).Select(BigInteger.Zero)) < ((byte)(64)));
          }
        }
        {
          if (_source0.is_TypeRGBA) {
            return ((new BigInteger((bits).Count)) == (new BigInteger(5))) && (((bits).Select(BigInteger.Zero)) == ((byte)(255)));
          }
        }
        {
          return ((new BigInteger((bits).Count)) == (new BigInteger(4))) && (((bits).Select(BigInteger.Zero)) == ((byte)(254)));
        }
      }))());
    }
    public static _IOp decodeBits(Dafny.ISequence<byte> bits) {
      _IOpType _source0 = __default.opTypeOfBits((bits).Select(BigInteger.Zero));
      {
        if (_source0.is_TypeRun) {
          return _module.Op.create_OpRun((byte)((byte)(((byte)(((byte)(((bits).Select(BigInteger.Zero)) - ((byte)(128)))) - ((byte)(64)))) + ((byte)(1)))));
        }
      }
      {
        if (_source0.is_TypeLuma) {
          return _module.Op.create_OpLuma(_module.RGBLuma.create((short)((new BigInteger((byte)(((bits).Select(BigInteger.One)) / ((byte)(16))))) - (new BigInteger(8))), (short)((new BigInteger((byte)(((bits).Select(BigInteger.Zero)) - ((byte)(128))))) - (new BigInteger(32))), (short)((new BigInteger((byte)(((bits).Select(BigInteger.One)) % ((byte)(16))))) - (new BigInteger(8)))));
        }
      }
      {
        if (_source0.is_TypeDiff) {
          return _module.Op.create_OpDiff(_module.RGBDiff.create((short)((new BigInteger((byte)(((byte)(((bits).Select(BigInteger.Zero)) - ((byte)(64)))) / ((byte)(16))))) - (new BigInteger(2))), (short)((new BigInteger((byte)(((byte)(((bits).Select(BigInteger.Zero)) / ((byte)(4)))) % ((byte)(4))))) - (new BigInteger(2))), (short)((new BigInteger((byte)(((bits).Select(BigInteger.Zero)) % ((byte)(4))))) - (new BigInteger(2)))));
        }
      }
      {
        if (_source0.is_TypeIndex) {
          return _module.Op.create_OpIndex((byte)((bits).Select(BigInteger.Zero)));
        }
      }
      {
        if (_source0.is_TypeRGBA) {
          return _module.Op.create_OpRGBA(_module.RGBA.create((bits).Select(BigInteger.One), (bits).Select(new BigInteger(2)), (bits).Select(new BigInteger(3)), (bits).Select(new BigInteger(4))));
        }
      }
      {
        return _module.Op.create_OpRGB(_module.RGB.create((bits).Select(BigInteger.One), (bits).Select(new BigInteger(2)), (bits).Select(new BigInteger(3))));
      }
    }
    public static bool validBitSeq(Dafny.ISequence<byte> bits) {
      var _pat_let_tv0 = bits;
      var _pat_let_tv1 = bits;
      var _pat_let_tv2 = bits;
      return ((new BigInteger((bits).Count)).Sign == 0) || (Dafny.Helpers.Let<BigInteger, bool>(__default.sizeBitEncoding(__default.opTypeOfBits((bits).Select(BigInteger.Zero))), _pat_let0_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let0_0, _0_len => (((new BigInteger((_pat_let_tv0).Count)) >= (_0_len)) && (__default.validBits((_pat_let_tv1).Subsequence(BigInteger.Zero, _0_len)))) && (__default.validBitSeq((_pat_let_tv2).Drop(_0_len))))));
    }
    public static Dafny.ISequence<byte> encodeBitSeq(Dafny.ISequence<_IOp> ops) {
      Dafny.ISequence<byte> _0___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ops).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_0___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<byte>.Concat(_0___accumulator, __default.encodeBits((ops).Select(BigInteger.Zero)));
        Dafny.ISequence<_IOp> _in0 = (ops).Drop(BigInteger.One);
        ops = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<_IOp> decodeBitSeqSure(Dafny.ISequence<byte> bits) {
      Dafny.ISequence<_IOp> _0___accumulator = Dafny.Sequence<_IOp>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((bits).Count)).Sign == 0) {
        return Dafny.Sequence<_IOp>.Concat(_0___accumulator, Dafny.Sequence<_IOp>.FromElements());
      } else {
        BigInteger _1_len = __default.sizeBitEncoding(__default.opTypeOfBits((bits).Select(BigInteger.Zero)));
        _0___accumulator = Dafny.Sequence<_IOp>.Concat(_0___accumulator, Dafny.Sequence<_IOp>.FromElements(__default.decodeBits((bits).Subsequence(BigInteger.Zero, _1_len))));
        Dafny.ISequence<byte> _in0 = (bits).Drop(_1_len);
        bits = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static _IOption<Dafny.ISequence<_IOp>> decodeBitSeq(Dafny.ISequence<byte> bits)
    {
      _IOption<Dafny.ISequence<_IOp>> r = Option<Dafny.ISequence<_IOp>>.Default();
      if ((new BigInteger((bits).Count)).Sign == 0) {
        r = _module.Option<Dafny.ISequence<_IOp>>.create_Some(Dafny.Sequence<_IOp>.FromElements());
      } else {
        BigInteger _0_len;
        _0_len = __default.sizeBitEncoding(__default.opTypeOfBits((bits).Select(BigInteger.Zero)));
        if ((new BigInteger((bits).Count)) < (_0_len)) {
          r = _module.Option<Dafny.ISequence<_IOp>>.create_None();
          return r;
        } else {
          if (__default.validBits((bits).Subsequence(BigInteger.Zero, _0_len))) {
            _IOption<Dafny.ISequence<_IOp>> _1_rec;
            _IOption<Dafny.ISequence<_IOp>> _out0;
            _out0 = __default.decodeBitSeq((bits).Drop(_0_len));
            _1_rec = _out0;
            if ((_1_rec).is_None) {
              r = _module.Option<Dafny.ISequence<_IOp>>.create_None();
              return r;
            } else {
              r = _module.Option<Dafny.ISequence<_IOp>>.create_Some(Dafny.Sequence<_IOp>.Concat(Dafny.Sequence<_IOp>.FromElements(__default.decodeBits((bits).Subsequence(BigInteger.Zero, _0_len))), (_1_rec).dtor_some));
            }
          } else {
            r = _module.Option<Dafny.ISequence<_IOp>>.create_None();
            return r;
          }
        }
      }
      return r;
    }
    public static Dafny.ISequence<byte> genHeader(_IDesc desc) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('q')).Value), (byte)((new Dafny.Rune('o')).Value), (byte)((new Dafny.Rune('i')).Value), (byte)((new Dafny.Rune('f')).Value)), __default.unpack((desc).dtor_width)), __default.unpack((desc).dtor_height)), Dafny.Sequence<byte>.FromElements((byte)((desc).dtor_channels))), Dafny.Sequence<byte>.FromElements(__default.byteFromColorSpace((desc).dtor_colorSpace)));
    }
    public static bool validHeader(Dafny.ISequence<byte> bits) {
      return ((((new BigInteger((bits).Count)) == (new BigInteger(14))) && (((bits).Subsequence(BigInteger.Zero, new BigInteger(4))).Equals(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('q')).Value), (byte)((new Dafny.Rune('o')).Value), (byte)((new Dafny.Rune('i')).Value), (byte)((new Dafny.Rune('f')).Value))))) && ((((byte)(3)) <= ((bits).Select(new BigInteger(12)))) && (((bits).Select(new BigInteger(12))) <= ((byte)(4))))) && ((((byte)(0)) <= ((bits).Select(new BigInteger(13)))) && (((bits).Select(new BigInteger(13))) <= ((byte)(1))));
    }
    public static _IDesc specHeader(Dafny.ISequence<byte> header) {
      return _module.Desc.create(__default.pack((header).Subsequence(new BigInteger(4), new BigInteger(8))), __default.pack((header).Subsequence(new BigInteger(8), new BigInteger(12))), (byte)((header).Select(new BigInteger(12))), __default.colorSpaceFromByte((header).Select(new BigInteger(13))));
    }
    public static Dafny.ISequence<byte> genFooter() {
      return Dafny.Sequence<byte>.Concat(((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim1 = new BigInteger(7);
        var arr1 = new byte[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
        for (int i1 = 0; i1 < dim1; i1++) {
          var _0_i = (BigInteger) i1;
          arr1[(int)(_0_i)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr1);
      }))(), Dafny.Sequence<byte>.FromElements((byte)(1)));
    }
    public static bool validFooter(Dafny.ISequence<byte> bits) {
      return (bits).Equals(__default.genFooter());
    }
    public static bool validByteStream(Dafny.ISequence<byte> byteStream) {
      BigInteger _0_len = new BigInteger((byteStream).Count);
      return (((((new BigInteger((byteStream).Count)) >= ((new BigInteger(14)) + (new BigInteger(8)))) && (__default.validHeader((byteStream).Take(new BigInteger(14))))) && (__default.validFooter((byteStream).Drop((_0_len) - (new BigInteger(8)))))) && (__default.validBitSeq((byteStream).Subsequence(new BigInteger(14), (_0_len) - (new BigInteger(8)))))) && ((new BigInteger((__default.specOps(__default.decodeBitSeqSure((byteStream).Subsequence(new BigInteger(14), (_0_len) - (new BigInteger(8)))))).Count)) == ((new BigInteger((__default.specHeader((byteStream).Take(new BigInteger(14)))).dtor_width)) * (new BigInteger((__default.specHeader((byteStream).Take(new BigInteger(14)))).dtor_height))));
    }
    public static _IImage specEndToEnd(Dafny.ISequence<byte> byteStream) {
      _IDesc _0_desc = __default.specHeader((byteStream).Take(new BigInteger(14)));
      BigInteger _1_len = new BigInteger((byteStream).Count);
      return _module.Image.create(_0_desc, __default.toByteStream(_0_desc, __default.specOps(__default.decodeBitSeqSure((byteStream).Subsequence(new BigInteger(14), (_1_len) - (new BigInteger(8)))))));
    }
    public static byte byteFromColorSpace(_IColorSpace colorSpace) {
      _IColorSpace _source0 = colorSpace;
      {
        if (_source0.is_SRGB) {
          return (byte)(0);
        }
      }
      {
        return (byte)(1);
      }
    }
    public static bool validColorSpaceAsByte(byte b) {
      return ((b) == ((byte)(0))) || ((b) == ((byte)(1)));
    }
    public static _IColorSpace colorSpaceFromByte(byte b) {
      if ((b) == ((byte)(0))) {
        return _module.ColorSpace.create_SRGB();
      } else {
        return _module.ColorSpace.create_Linear();
      }
    }
    public static byte hashRGBA(_IRGBA color) {
      return (byte)(Dafny.Helpers.EuclideanModulus(((((new BigInteger((color).dtor_r)) * (new BigInteger(3))) + ((new BigInteger((color).dtor_g)) * (new BigInteger(5)))) + ((new BigInteger((color).dtor_b)) * (new BigInteger(7)))) + ((new BigInteger((color).dtor_a)) * (new BigInteger(11))), new BigInteger(64)));
    }
    public static byte hash(_IRGB color) {
      return __default.hashRGBA(_module.RGBA.create((color).dtor_r, (color).dtor_g, (color).dtor_b, (byte)(255)));
    }
    public static bool validImage(_IImage image) {
      return (new BigInteger(((image).dtor_data).Count)) == (((new BigInteger(((image).dtor_desc).dtor_width)) * (new BigInteger(((image).dtor_desc).dtor_height))) * (new BigInteger(((image).dtor_desc).dtor_channels)));
    }
    public static _IState updateState(_IState previous, _IRGBA pixel)
    {
      return _module.State.create(pixel, Dafny.Sequence<_IRGBA>.Update((previous).dtor_index, __default.hashRGBA(pixel), pixel));
    }
    public static _IState initState() {
      return _module.State.create(_module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(255)), ((System.Func<Dafny.ISequence<_IRGBA>>) (() => {
  BigInteger dim2 = new BigInteger(64);
  var arr2 = new _IRGBA[Dafny.Helpers.ToIntChecked(dim2, "array size exceeds memory limit")];
  for (int i2 = 0; i2 < dim2; i2++) {
    var _0_i = (BigInteger) i2;
    arr2[(int)(_0_i)] = _module.RGBA.create((byte)(0), (byte)(0), (byte)(0), (byte)(255));
  }
  return Dafny.Sequence<_IRGBA>.FromArray(arr2);
}))());
    }
    public static _IState updateStateStar(_IState previous, Dafny.ISequence<_IRGBA> pixels)
    {
      if ((new BigInteger((pixels).Count)).Sign == 0) {
        return previous;
      } else {
        return __default.updateState(__default.updateStateStar(previous, (pixels).Take((new BigInteger((pixels).Count)) - (BigInteger.One))), (pixels).Select((new BigInteger((pixels).Count)) - (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<_IRGBA> specDecodeOp(_IState state, _IOp op)
    {
      _IOp _source0 = op;
      {
        if (_source0.is_OpRGB) {
          _IRGB rgb0 = _source0.dtor_rgb;
          byte _0_r = rgb0.dtor_r;
          byte _1_g = rgb0.dtor_g;
          byte _2_b = rgb0.dtor_b;
          return Dafny.Sequence<_IRGBA>.FromElements(_module.RGBA.create(_0_r, _1_g, _2_b, ((state).dtor_prev).dtor_a));
        }
      }
      {
        if (_source0.is_OpRun) {
          byte _3_size = _source0.dtor_size;
          return ((System.Func<Dafny.ISequence<_IRGBA>>) (() => {
            byte dim3 = _3_size;
            var arr3 = new _IRGBA[Dafny.Helpers.ToIntChecked(dim3, "array size exceeds memory limit")];
            for (int i3 = 0; i3 < dim3; i3++) {
              var _4_i = (byte) i3;
              arr3[(int)(_4_i)] = (state).dtor_prev;
            }
            return Dafny.Sequence<_IRGBA>.FromArray(arr3);
          }))();
        }
      }
      {
        if (_source0.is_OpIndex) {
          byte _5_index = _source0.dtor_index;
          return Dafny.Sequence<_IRGBA>.FromElements(((state).dtor_index).Select(_5_index));
        }
      }
      {
        if (_source0.is_OpDiff) {
          _IRGBDiff diff0 = _source0.dtor_diff;
          short _6_dr = diff0.dtor_dr;
          short _7_dg = diff0.dtor_dg;
          short _8_db = diff0.dtor_db;
          return Dafny.Sequence<_IRGBA>.FromElements(_module.RGBA.create(__default.add__byte(((state).dtor_prev).dtor_r, __default.byte__from(new BigInteger(_6_dr))), __default.add__byte(((state).dtor_prev).dtor_g, __default.byte__from(new BigInteger(_7_dg))), __default.add__byte(((state).dtor_prev).dtor_b, __default.byte__from(new BigInteger(_8_db))), ((state).dtor_prev).dtor_a));
        }
      }
      {
        if (_source0.is_OpLuma) {
          _IRGBLuma luma0 = _source0.dtor_luma;
          short _9_dr = luma0.dtor_dr;
          short _10_dg = luma0.dtor_dg;
          short _11_db = luma0.dtor_db;
          return Dafny.Sequence<_IRGBA>.FromElements(_module.RGBA.create(__default.add__byte(__default.add__byte(((state).dtor_prev).dtor_r, __default.byte__from(new BigInteger(_10_dg))), __default.byte__from(new BigInteger(_9_dr))), __default.add__byte(((state).dtor_prev).dtor_g, __default.byte__from(new BigInteger(_10_dg))), __default.add__byte(__default.add__byte(((state).dtor_prev).dtor_b, __default.byte__from(new BigInteger(_10_dg))), __default.byte__from(new BigInteger(_11_db))), ((state).dtor_prev).dtor_a));
        }
      }
      {
        _IRGBA _12_rgba = _source0.dtor_rgba;
        return Dafny.Sequence<_IRGBA>.FromElements(_12_rgba);
      }
    }
    public static Dafny.ISequence<_IRGBA> specOpsAux(Dafny.ISequence<_IOp> ops, _IState state)
    {
      Dafny.ISequence<_IRGBA> _0___accumulator = Dafny.Sequence<_IRGBA>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ops).Count)).Sign == 0) {
        return Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, Dafny.Sequence<_IRGBA>.FromElements());
      } else {
        Dafny.ISequence<_IRGBA> _1_pixels = __default.specDecodeOp(state, (ops).Select(BigInteger.Zero));
        _0___accumulator = Dafny.Sequence<_IRGBA>.Concat(_0___accumulator, _1_pixels);
        Dafny.ISequence<_IOp> _in0 = (ops).Drop(BigInteger.One);
        _IState _in1 = __default.updateStateStar(state, _1_pixels);
        ops = _in0;
        state = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<_IRGBA> specOps(Dafny.ISequence<_IOp> ops) {
      return __default.specOpsAux(ops, __default.initState());
    }
    public static Dafny.ISequence<byte> toByteStreamRGB(Dafny.ISequence<_IRGBA> data) {
      Dafny.ISequence<byte> _0___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((data).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_0___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<byte>.Concat(_0___accumulator, Dafny.Sequence<byte>.FromElements(((data).Select(BigInteger.Zero)).dtor_r, ((data).Select(BigInteger.Zero)).dtor_g, ((data).Select(BigInteger.Zero)).dtor_b));
        Dafny.ISequence<_IRGBA> _in0 = (data).Drop(BigInteger.One);
        data = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> toByteStreamRGBA(Dafny.ISequence<_IRGBA> data) {
      Dafny.ISequence<byte> _0___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((data).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_0___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<byte>.Concat(_0___accumulator, Dafny.Sequence<byte>.FromElements(((data).Select(BigInteger.Zero)).dtor_r, ((data).Select(BigInteger.Zero)).dtor_g, ((data).Select(BigInteger.Zero)).dtor_b, ((data).Select(BigInteger.Zero)).dtor_a));
        Dafny.ISequence<_IRGBA> _in0 = (data).Drop(BigInteger.One);
        data = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> toByteStream(_IDesc desc, Dafny.ISequence<_IRGBA> data)
    {
      byte _source0 = (desc).dtor_channels;
      {
        if ((_source0) == ((byte)(3))) {
          return __default.toByteStreamRGB(data);
        }
      }
      {
        return __default.toByteStreamRGBA(data);
      }
    }
    public static bool validAEI(_IAEI aei) {
      return (new BigInteger((__default.specOps((aei).dtor_ops)).Count)) == ((new BigInteger((aei).dtor_width)) * (new BigInteger((aei).dtor_height)));
    }
    public static Dafny.ISequence<_IRGBA> spec(_IAEI aei) {
      return __default.specOps((aei).dtor_ops);
    }
    public static byte add__byte(byte x, byte y)
    {
      return (byte)(Dafny.Helpers.EuclideanModulus((new BigInteger(x)) + (new BigInteger(y)), new BigInteger(256)));
    }
    public static byte sub__byte(byte x, byte y)
    {
      return (byte)(Dafny.Helpers.EuclideanModulus((new BigInteger(x)) + ((new BigInteger(256)) - (new BigInteger(y))), new BigInteger(256)));
    }
    public static byte byte__from(BigInteger x) {
      return (byte)(Dafny.Helpers.EuclideanModulus(x, new BigInteger(256)));
    }
    public static Dafny.ISequence<byte> unpack(uint x) {
      byte _0_b0 = (byte)(((x) / (((256U) * (256U)) * (256U))) % (256U));
      byte _1_b1 = (byte)(((x) / ((256U) * (256U))) % (256U));
      byte _2_b2 = (byte)(((x) / (256U)) % (256U));
      byte _3_b3 = (byte)((x) % (256U));
      return Dafny.Sequence<byte>.FromElements(_0_b0, _1_b1, _2_b2, _3_b3);
    }
    public static uint pack(Dafny.ISequence<byte> x) {
      return (((((uint)((x).Select(BigInteger.Zero))) * (16777216U)) + (((uint)((x).Select(BigInteger.One))) * (65536U))) + (((uint)((x).Select(new BigInteger(2)))) * (256U))) + ((uint)((x).Select(new BigInteger(3))));
    }
  }

  public interface _IOpChain {
    bool is_EmptyOp { get; }
    bool is_LinkOp { get; }
    _IOp dtor_op { get; }
    _IOpChain dtor_next { get; }
    _IOpChain DowncastClone();
  }
  public abstract class OpChain : _IOpChain {
    public OpChain() {
    }
    private static readonly _IOpChain theDefault = create_EmptyOp();
    public static _IOpChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IOpChain> _TYPE = new Dafny.TypeDescriptor<_IOpChain>(OpChain.Default());
    public static Dafny.TypeDescriptor<_IOpChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOpChain create_EmptyOp() {
      return new OpChain_EmptyOp();
    }
    public static _IOpChain create_LinkOp(_IOp op, _IOpChain next) {
      return new OpChain_LinkOp(op, next);
    }
    public bool is_EmptyOp { get { return this is OpChain_EmptyOp; } }
    public bool is_LinkOp { get { return this is OpChain_LinkOp; } }
    public _IOp dtor_op {
      get {
        var d = this;
        return ((OpChain_LinkOp)d)._op;
      }
    }
    public _IOpChain dtor_next {
      get {
        var d = this;
        return ((OpChain_LinkOp)d)._next;
      }
    }
    public abstract _IOpChain DowncastClone();
  }
  public class OpChain_EmptyOp : OpChain {
    public OpChain_EmptyOp() : base() {
    }
    public override _IOpChain DowncastClone() {
      if (this is _IOpChain dt) { return dt; }
      return new OpChain_EmptyOp();
    }
    public override bool Equals(object other) {
      var oth = other as OpChain_EmptyOp;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpChain.EmptyOp";
      return s;
    }
  }
  public class OpChain_LinkOp : OpChain {
    public readonly _IOp _op;
    public readonly _IOpChain _next;
    public OpChain_LinkOp(_IOp op, _IOpChain next) : base() {
      this._op = op;
      this._next = next;
    }
    public override _IOpChain DowncastClone() {
      if (this is _IOpChain dt) { return dt; }
      return new OpChain_LinkOp(_op, _next);
    }
    public override bool Equals(object other) {
      var oth = other as OpChain_LinkOp;
      return oth != null && object.Equals(this._op, oth._op) && object.Equals(this._next, oth._next);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._next));
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpChain.LinkOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._op);
      s += ", ";
      s += Dafny.Helpers.ToString(this._next);
      s += ")";
      return s;
    }
  }

  public interface _IByteChain {
    bool is_EmptyByte { get; }
    bool is_LinkByte { get; }
    Dafny.ISequence<byte> dtor_data { get; }
    _IByteChain dtor_next { get; }
    _IByteChain DowncastClone();
  }
  public abstract class ByteChain : _IByteChain {
    public ByteChain() {
    }
    private static readonly _IByteChain theDefault = create_EmptyByte();
    public static _IByteChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IByteChain> _TYPE = new Dafny.TypeDescriptor<_IByteChain>(ByteChain.Default());
    public static Dafny.TypeDescriptor<_IByteChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IByteChain create_EmptyByte() {
      return new ByteChain_EmptyByte();
    }
    public static _IByteChain create_LinkByte(Dafny.ISequence<byte> data, _IByteChain next) {
      return new ByteChain_LinkByte(data, next);
    }
    public bool is_EmptyByte { get { return this is ByteChain_EmptyByte; } }
    public bool is_LinkByte { get { return this is ByteChain_LinkByte; } }
    public Dafny.ISequence<byte> dtor_data {
      get {
        var d = this;
        return ((ByteChain_LinkByte)d)._data;
      }
    }
    public _IByteChain dtor_next {
      get {
        var d = this;
        return ((ByteChain_LinkByte)d)._next;
      }
    }
    public abstract _IByteChain DowncastClone();
  }
  public class ByteChain_EmptyByte : ByteChain {
    public ByteChain_EmptyByte() : base() {
    }
    public override _IByteChain DowncastClone() {
      if (this is _IByteChain dt) { return dt; }
      return new ByteChain_EmptyByte();
    }
    public override bool Equals(object other) {
      var oth = other as ByteChain_EmptyByte;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ByteChain.EmptyByte";
      return s;
    }
  }
  public class ByteChain_LinkByte : ByteChain {
    public readonly Dafny.ISequence<byte> _data;
    public readonly _IByteChain _next;
    public ByteChain_LinkByte(Dafny.ISequence<byte> data, _IByteChain next) : base() {
      this._data = data;
      this._next = next;
    }
    public override _IByteChain DowncastClone() {
      if (this is _IByteChain dt) { return dt; }
      return new ByteChain_LinkByte(_data, _next);
    }
    public override bool Equals(object other) {
      var oth = other as ByteChain_LinkByte;
      return oth != null && object.Equals(this._data, oth._data) && object.Equals(this._next, oth._next);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._next));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ByteChain.LinkByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._data);
      s += ", ";
      s += Dafny.Helpers.ToString(this._next);
      s += ")";
      return s;
    }
  }

  public interface _IOpType {
    bool is_TypeRun { get; }
    bool is_TypeIndex { get; }
    bool is_TypeDiff { get; }
    bool is_TypeLuma { get; }
    bool is_TypeRGB { get; }
    bool is_TypeRGBA { get; }
    _IOpType DowncastClone();
  }
  public abstract class OpType : _IOpType {
    public OpType() {
    }
    private static readonly _IOpType theDefault = create_TypeRun();
    public static _IOpType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IOpType> _TYPE = new Dafny.TypeDescriptor<_IOpType>(OpType.Default());
    public static Dafny.TypeDescriptor<_IOpType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOpType create_TypeRun() {
      return new OpType_TypeRun();
    }
    public static _IOpType create_TypeIndex() {
      return new OpType_TypeIndex();
    }
    public static _IOpType create_TypeDiff() {
      return new OpType_TypeDiff();
    }
    public static _IOpType create_TypeLuma() {
      return new OpType_TypeLuma();
    }
    public static _IOpType create_TypeRGB() {
      return new OpType_TypeRGB();
    }
    public static _IOpType create_TypeRGBA() {
      return new OpType_TypeRGBA();
    }
    public bool is_TypeRun { get { return this is OpType_TypeRun; } }
    public bool is_TypeIndex { get { return this is OpType_TypeIndex; } }
    public bool is_TypeDiff { get { return this is OpType_TypeDiff; } }
    public bool is_TypeLuma { get { return this is OpType_TypeLuma; } }
    public bool is_TypeRGB { get { return this is OpType_TypeRGB; } }
    public bool is_TypeRGBA { get { return this is OpType_TypeRGBA; } }
    public static System.Collections.Generic.IEnumerable<_IOpType> AllSingletonConstructors {
      get {
        yield return OpType.create_TypeRun();
        yield return OpType.create_TypeIndex();
        yield return OpType.create_TypeDiff();
        yield return OpType.create_TypeLuma();
        yield return OpType.create_TypeRGB();
        yield return OpType.create_TypeRGBA();
      }
    }
    public abstract _IOpType DowncastClone();
  }
  public class OpType_TypeRun : OpType {
    public OpType_TypeRun() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeRun();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeRun;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeRun";
      return s;
    }
  }
  public class OpType_TypeIndex : OpType {
    public OpType_TypeIndex() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeIndex();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeIndex;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeIndex";
      return s;
    }
  }
  public class OpType_TypeDiff : OpType {
    public OpType_TypeDiff() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeDiff();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeDiff;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeDiff";
      return s;
    }
  }
  public class OpType_TypeLuma : OpType {
    public OpType_TypeLuma() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeLuma();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeLuma;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeLuma";
      return s;
    }
  }
  public class OpType_TypeRGB : OpType {
    public OpType_TypeRGB() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeRGB();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeRGB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeRGB";
      return s;
    }
  }
  public class OpType_TypeRGBA : OpType {
    public OpType_TypeRGBA() : base() {
    }
    public override _IOpType DowncastClone() {
      if (this is _IOpType dt) { return dt; }
      return new OpType_TypeRGBA();
    }
    public override bool Equals(object other) {
      var oth = other as OpType_TypeRGBA;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "OpType.TypeRGBA";
      return s;
    }
  }

  public interface _IRGB {
    bool is_RGB { get; }
    byte dtor_r { get; }
    byte dtor_g { get; }
    byte dtor_b { get; }
    _IRGB DowncastClone();
  }
  public class RGB : _IRGB {
    public readonly byte _r;
    public readonly byte _g;
    public readonly byte _b;
    public RGB(byte r, byte g, byte b) {
      this._r = r;
      this._g = g;
      this._b = b;
    }
    public _IRGB DowncastClone() {
      if (this is _IRGB dt) { return dt; }
      return new RGB(_r, _g, _b);
    }
    public override bool Equals(object other) {
      var oth = other as RGB;
      return oth != null && this._r == oth._r && this._g == oth._g && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._g));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RGB.RGB";
      s += "(";
      s += Dafny.Helpers.ToString(this._r);
      s += ", ";
      s += Dafny.Helpers.ToString(this._g);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
    private static readonly _IRGB theDefault = create(0, 0, 0);
    public static _IRGB Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IRGB> _TYPE = new Dafny.TypeDescriptor<_IRGB>(RGB.Default());
    public static Dafny.TypeDescriptor<_IRGB> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRGB create(byte r, byte g, byte b) {
      return new RGB(r, g, b);
    }
    public static _IRGB create_RGB(byte r, byte g, byte b) {
      return create(r, g, b);
    }
    public bool is_RGB { get { return true; } }
    public byte dtor_r {
      get {
        return this._r;
      }
    }
    public byte dtor_g {
      get {
        return this._g;
      }
    }
    public byte dtor_b {
      get {
        return this._b;
      }
    }
  }

  public interface _IRGBA {
    bool is_RGBA { get; }
    byte dtor_r { get; }
    byte dtor_g { get; }
    byte dtor_b { get; }
    byte dtor_a { get; }
    _IRGBA DowncastClone();
  }
  public class RGBA : _IRGBA {
    public readonly byte _r;
    public readonly byte _g;
    public readonly byte _b;
    public readonly byte _a;
    public RGBA(byte r, byte g, byte b, byte a) {
      this._r = r;
      this._g = g;
      this._b = b;
      this._a = a;
    }
    public _IRGBA DowncastClone() {
      if (this is _IRGBA dt) { return dt; }
      return new RGBA(_r, _g, _b, _a);
    }
    public override bool Equals(object other) {
      var oth = other as RGBA;
      return oth != null && this._r == oth._r && this._g == oth._g && this._b == oth._b && this._a == oth._a;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._g));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RGBA.RGBA";
      s += "(";
      s += Dafny.Helpers.ToString(this._r);
      s += ", ";
      s += Dafny.Helpers.ToString(this._g);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ", ";
      s += Dafny.Helpers.ToString(this._a);
      s += ")";
      return s;
    }
    private static readonly _IRGBA theDefault = create(0, 0, 0, 0);
    public static _IRGBA Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IRGBA> _TYPE = new Dafny.TypeDescriptor<_IRGBA>(RGBA.Default());
    public static Dafny.TypeDescriptor<_IRGBA> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRGBA create(byte r, byte g, byte b, byte a) {
      return new RGBA(r, g, b, a);
    }
    public static _IRGBA create_RGBA(byte r, byte g, byte b, byte a) {
      return create(r, g, b, a);
    }
    public bool is_RGBA { get { return true; } }
    public byte dtor_r {
      get {
        return this._r;
      }
    }
    public byte dtor_g {
      get {
        return this._g;
      }
    }
    public byte dtor_b {
      get {
        return this._b;
      }
    }
    public byte dtor_a {
      get {
        return this._a;
      }
    }
  }

  public partial class Channels {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    public static readonly byte Witness = (byte)(new BigInteger(3));
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(Channels.Witness);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(byte __source) {
      BigInteger _0_x = new BigInteger(__source);
      return ((new BigInteger(3)) <= (_0_x)) && ((_0_x) <= (new BigInteger(4)));
    }
  }

  public interface _IColorSpace {
    bool is_SRGB { get; }
    bool is_Linear { get; }
    _IColorSpace DowncastClone();
  }
  public abstract class ColorSpace : _IColorSpace {
    public ColorSpace() {
    }
    private static readonly _IColorSpace theDefault = create_SRGB();
    public static _IColorSpace Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IColorSpace> _TYPE = new Dafny.TypeDescriptor<_IColorSpace>(ColorSpace.Default());
    public static Dafny.TypeDescriptor<_IColorSpace> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IColorSpace create_SRGB() {
      return new ColorSpace_SRGB();
    }
    public static _IColorSpace create_Linear() {
      return new ColorSpace_Linear();
    }
    public bool is_SRGB { get { return this is ColorSpace_SRGB; } }
    public bool is_Linear { get { return this is ColorSpace_Linear; } }
    public static System.Collections.Generic.IEnumerable<_IColorSpace> AllSingletonConstructors {
      get {
        yield return ColorSpace.create_SRGB();
        yield return ColorSpace.create_Linear();
      }
    }
    public abstract _IColorSpace DowncastClone();
  }
  public class ColorSpace_SRGB : ColorSpace {
    public ColorSpace_SRGB() : base() {
    }
    public override _IColorSpace DowncastClone() {
      if (this is _IColorSpace dt) { return dt; }
      return new ColorSpace_SRGB();
    }
    public override bool Equals(object other) {
      var oth = other as ColorSpace_SRGB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ColorSpace.SRGB";
      return s;
    }
  }
  public class ColorSpace_Linear : ColorSpace {
    public ColorSpace_Linear() : base() {
    }
    public override _IColorSpace DowncastClone() {
      if (this is _IColorSpace dt) { return dt; }
      return new ColorSpace_Linear();
    }
    public override bool Equals(object other) {
      var oth = other as ColorSpace_Linear;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ColorSpace.Linear";
      return s;
    }
  }

  public interface _IDesc {
    bool is_Desc { get; }
    uint dtor_width { get; }
    uint dtor_height { get; }
    byte dtor_channels { get; }
    _IColorSpace dtor_colorSpace { get; }
    _IDesc DowncastClone();
  }
  public class Desc : _IDesc {
    public readonly uint _width;
    public readonly uint _height;
    public readonly byte _channels;
    public readonly _IColorSpace _colorSpace;
    public Desc(uint width, uint height, byte channels, _IColorSpace colorSpace) {
      this._width = width;
      this._height = height;
      this._channels = channels;
      this._colorSpace = colorSpace;
    }
    public _IDesc DowncastClone() {
      if (this is _IDesc dt) { return dt; }
      return new Desc(_width, _height, _channels, _colorSpace);
    }
    public override bool Equals(object other) {
      var oth = other as Desc;
      return oth != null && this._width == oth._width && this._height == oth._height && this._channels == oth._channels && object.Equals(this._colorSpace, oth._colorSpace);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._width));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._height));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._channels));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._colorSpace));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Desc.Desc";
      s += "(";
      s += Dafny.Helpers.ToString(this._width);
      s += ", ";
      s += Dafny.Helpers.ToString(this._height);
      s += ", ";
      s += Dafny.Helpers.ToString(this._channels);
      s += ", ";
      s += Dafny.Helpers.ToString(this._colorSpace);
      s += ")";
      return s;
    }
    private static readonly _IDesc theDefault = create(0, 0, Channels.Witness, ColorSpace.Default());
    public static _IDesc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IDesc> _TYPE = new Dafny.TypeDescriptor<_IDesc>(Desc.Default());
    public static Dafny.TypeDescriptor<_IDesc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDesc create(uint width, uint height, byte channels, _IColorSpace colorSpace) {
      return new Desc(width, height, channels, colorSpace);
    }
    public static _IDesc create_Desc(uint width, uint height, byte channels, _IColorSpace colorSpace) {
      return create(width, height, channels, colorSpace);
    }
    public bool is_Desc { get { return true; } }
    public uint dtor_width {
      get {
        return this._width;
      }
    }
    public uint dtor_height {
      get {
        return this._height;
      }
    }
    public byte dtor_channels {
      get {
        return this._channels;
      }
    }
    public _IColorSpace dtor_colorSpace {
      get {
        return this._colorSpace;
      }
    }
  }

  public interface _IImage {
    bool is_Image { get; }
    _IDesc dtor_desc { get; }
    Dafny.ISequence<byte> dtor_data { get; }
    _IImage DowncastClone();
  }
  public class Image : _IImage {
    public readonly _IDesc _desc;
    public readonly Dafny.ISequence<byte> _data;
    public Image(_IDesc desc, Dafny.ISequence<byte> data) {
      this._desc = desc;
      this._data = data;
    }
    public _IImage DowncastClone() {
      if (this is _IImage dt) { return dt; }
      return new Image(_desc, _data);
    }
    public override bool Equals(object other) {
      var oth = other as Image;
      return oth != null && object.Equals(this._desc, oth._desc) && object.Equals(this._data, oth._data);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._desc));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Image.Image";
      s += "(";
      s += Dafny.Helpers.ToString(this._desc);
      s += ", ";
      s += Dafny.Helpers.ToString(this._data);
      s += ")";
      return s;
    }
    private static readonly _IImage theDefault = create(Desc.Default(), Dafny.Sequence<byte>.Empty);
    public static _IImage Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IImage> _TYPE = new Dafny.TypeDescriptor<_IImage>(Image.Default());
    public static Dafny.TypeDescriptor<_IImage> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImage create(_IDesc desc, Dafny.ISequence<byte> data) {
      return new Image(desc, data);
    }
    public static _IImage create_Image(_IDesc desc, Dafny.ISequence<byte> data) {
      return create(desc, data);
    }
    public bool is_Image { get { return true; } }
    public _IDesc dtor_desc {
      get {
        return this._desc;
      }
    }
    public Dafny.ISequence<byte> dtor_data {
      get {
        return this._data;
      }
    }
  }

  public partial class Size {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    public static readonly byte Witness = (byte)(BigInteger.One);
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(Size.Witness);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(byte __source) {
      BigInteger _1_x = new BigInteger(__source);
      return ((BigInteger.One) <= (_1_x)) && ((_1_x) <= (new BigInteger(62)));
    }
  }

  public partial class Index64 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(byte __source) {
      BigInteger _2_x = new BigInteger(__source);
      return ((_2_x).Sign != -1) && ((_2_x) <= (new BigInteger(63)));
    }
  }

  public partial class Diff64 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(short __source) {
      BigInteger _3_x = new BigInteger(__source);
      return ((new BigInteger(-32)) <= (_3_x)) && ((_3_x) <= (new BigInteger(31)));
    }
  }

  public partial class Diff16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(short __source) {
      BigInteger _4_x = new BigInteger(__source);
      return ((new BigInteger(-8)) <= (_4_x)) && ((_4_x) <= (new BigInteger(7)));
    }
  }

  public partial class Diff {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(short __source) {
      BigInteger _5_x = new BigInteger(__source);
      return ((new BigInteger(-2)) <= (_5_x)) && ((_5_x) <= (BigInteger.One));
    }
  }

  public interface _IRGBDiff {
    bool is_RGBDiff { get; }
    short dtor_dr { get; }
    short dtor_dg { get; }
    short dtor_db { get; }
    _IRGBDiff DowncastClone();
  }
  public class RGBDiff : _IRGBDiff {
    public readonly short _dr;
    public readonly short _dg;
    public readonly short _db;
    public RGBDiff(short dr, short dg, short db) {
      this._dr = dr;
      this._dg = dg;
      this._db = db;
    }
    public _IRGBDiff DowncastClone() {
      if (this is _IRGBDiff dt) { return dt; }
      return new RGBDiff(_dr, _dg, _db);
    }
    public override bool Equals(object other) {
      var oth = other as RGBDiff;
      return oth != null && this._dr == oth._dr && this._dg == oth._dg && this._db == oth._db;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._db));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RGBDiff.RGBDiff";
      s += "(";
      s += Dafny.Helpers.ToString(this._dr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._db);
      s += ")";
      return s;
    }
    private static readonly _IRGBDiff theDefault = create(0, 0, 0);
    public static _IRGBDiff Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IRGBDiff> _TYPE = new Dafny.TypeDescriptor<_IRGBDiff>(RGBDiff.Default());
    public static Dafny.TypeDescriptor<_IRGBDiff> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRGBDiff create(short dr, short dg, short db) {
      return new RGBDiff(dr, dg, db);
    }
    public static _IRGBDiff create_RGBDiff(short dr, short dg, short db) {
      return create(dr, dg, db);
    }
    public bool is_RGBDiff { get { return true; } }
    public short dtor_dr {
      get {
        return this._dr;
      }
    }
    public short dtor_dg {
      get {
        return this._dg;
      }
    }
    public short dtor_db {
      get {
        return this._db;
      }
    }
  }

  public interface _IRGBLuma {
    bool is_RGBLuma { get; }
    short dtor_dr { get; }
    short dtor_dg { get; }
    short dtor_db { get; }
    _IRGBLuma DowncastClone();
  }
  public class RGBLuma : _IRGBLuma {
    public readonly short _dr;
    public readonly short _dg;
    public readonly short _db;
    public RGBLuma(short dr, short dg, short db) {
      this._dr = dr;
      this._dg = dg;
      this._db = db;
    }
    public _IRGBLuma DowncastClone() {
      if (this is _IRGBLuma dt) { return dt; }
      return new RGBLuma(_dr, _dg, _db);
    }
    public override bool Equals(object other) {
      var oth = other as RGBLuma;
      return oth != null && this._dr == oth._dr && this._dg == oth._dg && this._db == oth._db;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._db));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RGBLuma.RGBLuma";
      s += "(";
      s += Dafny.Helpers.ToString(this._dr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._db);
      s += ")";
      return s;
    }
    private static readonly _IRGBLuma theDefault = create(0, 0, 0);
    public static _IRGBLuma Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IRGBLuma> _TYPE = new Dafny.TypeDescriptor<_IRGBLuma>(RGBLuma.Default());
    public static Dafny.TypeDescriptor<_IRGBLuma> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRGBLuma create(short dr, short dg, short db) {
      return new RGBLuma(dr, dg, db);
    }
    public static _IRGBLuma create_RGBLuma(short dr, short dg, short db) {
      return create(dr, dg, db);
    }
    public bool is_RGBLuma { get { return true; } }
    public short dtor_dr {
      get {
        return this._dr;
      }
    }
    public short dtor_dg {
      get {
        return this._dg;
      }
    }
    public short dtor_db {
      get {
        return this._db;
      }
    }
  }

  public interface _IOp {
    bool is_OpRun { get; }
    bool is_OpIndex { get; }
    bool is_OpDiff { get; }
    bool is_OpLuma { get; }
    bool is_OpRGB { get; }
    bool is_OpRGBA { get; }
    byte dtor_size { get; }
    byte dtor_index { get; }
    _IRGBDiff dtor_diff { get; }
    _IRGBLuma dtor_luma { get; }
    _IRGB dtor_rgb { get; }
    _IRGBA dtor_rgba { get; }
    _IOp DowncastClone();
  }
  public abstract class Op : _IOp {
    public Op() {
    }
    private static readonly _IOp theDefault = create_OpRun(Size.Witness);
    public static _IOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IOp> _TYPE = new Dafny.TypeDescriptor<_IOp>(Op.Default());
    public static Dafny.TypeDescriptor<_IOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOp create_OpRun(byte size) {
      return new Op_OpRun(size);
    }
    public static _IOp create_OpIndex(byte index) {
      return new Op_OpIndex(index);
    }
    public static _IOp create_OpDiff(_IRGBDiff diff) {
      return new Op_OpDiff(diff);
    }
    public static _IOp create_OpLuma(_IRGBLuma luma) {
      return new Op_OpLuma(luma);
    }
    public static _IOp create_OpRGB(_IRGB rgb) {
      return new Op_OpRGB(rgb);
    }
    public static _IOp create_OpRGBA(_IRGBA rgba) {
      return new Op_OpRGBA(rgba);
    }
    public bool is_OpRun { get { return this is Op_OpRun; } }
    public bool is_OpIndex { get { return this is Op_OpIndex; } }
    public bool is_OpDiff { get { return this is Op_OpDiff; } }
    public bool is_OpLuma { get { return this is Op_OpLuma; } }
    public bool is_OpRGB { get { return this is Op_OpRGB; } }
    public bool is_OpRGBA { get { return this is Op_OpRGBA; } }
    public byte dtor_size {
      get {
        var d = this;
        return ((Op_OpRun)d)._size;
      }
    }
    public byte dtor_index {
      get {
        var d = this;
        return ((Op_OpIndex)d)._index;
      }
    }
    public _IRGBDiff dtor_diff {
      get {
        var d = this;
        return ((Op_OpDiff)d)._diff;
      }
    }
    public _IRGBLuma dtor_luma {
      get {
        var d = this;
        return ((Op_OpLuma)d)._luma;
      }
    }
    public _IRGB dtor_rgb {
      get {
        var d = this;
        return ((Op_OpRGB)d)._rgb;
      }
    }
    public _IRGBA dtor_rgba {
      get {
        var d = this;
        return ((Op_OpRGBA)d)._rgba;
      }
    }
    public abstract _IOp DowncastClone();
  }
  public class Op_OpRun : Op {
    public readonly byte _size;
    public Op_OpRun(byte size) : base() {
      this._size = size;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpRun(_size);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpRun;
      return oth != null && this._size == oth._size;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._size));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpRun";
      s += "(";
      s += Dafny.Helpers.ToString(this._size);
      s += ")";
      return s;
    }
  }
  public class Op_OpIndex : Op {
    public readonly byte _index;
    public Op_OpIndex(byte index) : base() {
      this._index = index;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpIndex(_index);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpIndex;
      return oth != null && this._index == oth._index;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._index));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpIndex";
      s += "(";
      s += Dafny.Helpers.ToString(this._index);
      s += ")";
      return s;
    }
  }
  public class Op_OpDiff : Op {
    public readonly _IRGBDiff _diff;
    public Op_OpDiff(_IRGBDiff diff) : base() {
      this._diff = diff;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpDiff(_diff);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpDiff;
      return oth != null && object.Equals(this._diff, oth._diff);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._diff));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpDiff";
      s += "(";
      s += Dafny.Helpers.ToString(this._diff);
      s += ")";
      return s;
    }
  }
  public class Op_OpLuma : Op {
    public readonly _IRGBLuma _luma;
    public Op_OpLuma(_IRGBLuma luma) : base() {
      this._luma = luma;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpLuma(_luma);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpLuma;
      return oth != null && object.Equals(this._luma, oth._luma);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._luma));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpLuma";
      s += "(";
      s += Dafny.Helpers.ToString(this._luma);
      s += ")";
      return s;
    }
  }
  public class Op_OpRGB : Op {
    public readonly _IRGB _rgb;
    public Op_OpRGB(_IRGB rgb) : base() {
      this._rgb = rgb;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpRGB(_rgb);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpRGB;
      return oth != null && object.Equals(this._rgb, oth._rgb);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rgb));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpRGB";
      s += "(";
      s += Dafny.Helpers.ToString(this._rgb);
      s += ")";
      return s;
    }
  }
  public class Op_OpRGBA : Op {
    public readonly _IRGBA _rgba;
    public Op_OpRGBA(_IRGBA rgba) : base() {
      this._rgba = rgba;
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_OpRGBA(_rgba);
    }
    public override bool Equals(object other) {
      var oth = other as Op_OpRGBA;
      return oth != null && object.Equals(this._rgba, oth._rgba);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rgba));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.OpRGBA";
      s += "(";
      s += Dafny.Helpers.ToString(this._rgba);
      s += ")";
      return s;
    }
  }

  public interface _IAEI {
    bool is_AEI { get; }
    uint dtor_width { get; }
    uint dtor_height { get; }
    Dafny.ISequence<_IOp> dtor_ops { get; }
    _IAEI DowncastClone();
  }
  public class AEI : _IAEI {
    public readonly uint _width;
    public readonly uint _height;
    public readonly Dafny.ISequence<_IOp> _ops;
    public AEI(uint width, uint height, Dafny.ISequence<_IOp> ops) {
      this._width = width;
      this._height = height;
      this._ops = ops;
    }
    public _IAEI DowncastClone() {
      if (this is _IAEI dt) { return dt; }
      return new AEI(_width, _height, _ops);
    }
    public override bool Equals(object other) {
      var oth = other as AEI;
      return oth != null && this._width == oth._width && this._height == oth._height && object.Equals(this._ops, oth._ops);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._width));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._height));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ops));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AEI.AEI";
      s += "(";
      s += Dafny.Helpers.ToString(this._width);
      s += ", ";
      s += Dafny.Helpers.ToString(this._height);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ops);
      s += ")";
      return s;
    }
    private static readonly _IAEI theDefault = create(0, 0, Dafny.Sequence<_IOp>.Empty);
    public static _IAEI Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IAEI> _TYPE = new Dafny.TypeDescriptor<_IAEI>(AEI.Default());
    public static Dafny.TypeDescriptor<_IAEI> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAEI create(uint width, uint height, Dafny.ISequence<_IOp> ops) {
      return new AEI(width, height, ops);
    }
    public static _IAEI create_AEI(uint width, uint height, Dafny.ISequence<_IOp> ops) {
      return create(width, height, ops);
    }
    public bool is_AEI { get { return true; } }
    public uint dtor_width {
      get {
        return this._width;
      }
    }
    public uint dtor_height {
      get {
        return this._height;
      }
    }
    public Dafny.ISequence<_IOp> dtor_ops {
      get {
        return this._ops;
      }
    }
  }

  public interface _IState {
    bool is_State { get; }
    _IRGBA dtor_prev { get; }
    Dafny.ISequence<_IRGBA> dtor_index { get; }
    _IState DowncastClone();
  }
  public class State : _IState {
    public readonly _IRGBA _prev;
    public readonly Dafny.ISequence<_IRGBA> _index;
    public State(_IRGBA prev, Dafny.ISequence<_IRGBA> index) {
      this._prev = prev;
      this._index = index;
    }
    public _IState DowncastClone() {
      if (this is _IState dt) { return dt; }
      return new State(_prev, _index);
    }
    public override bool Equals(object other) {
      var oth = other as State;
      return oth != null && object.Equals(this._prev, oth._prev) && object.Equals(this._index, oth._index);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._prev));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._index));
      return (int) hash;
    }
    public override string ToString() {
      string s = "State.State";
      s += "(";
      s += Dafny.Helpers.ToString(this._prev);
      s += ", ";
      s += Dafny.Helpers.ToString(this._index);
      s += ")";
      return s;
    }
    private static readonly _IState theDefault = create(RGBA.Default(), Dafny.Sequence<_IRGBA>.Empty);
    public static _IState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IState> _TYPE = new Dafny.TypeDescriptor<_IState>(State.Default());
    public static Dafny.TypeDescriptor<_IState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IState create(_IRGBA prev, Dafny.ISequence<_IRGBA> index) {
      return new State(prev, index);
    }
    public static _IState create_State(_IRGBA prev, Dafny.ISequence<_IRGBA> index) {
      return create(prev, index);
    }
    public bool is_State { get { return true; } }
    public _IRGBA dtor_prev {
      get {
        return this._prev;
      }
    }
    public Dafny.ISequence<_IRGBA> dtor_index {
      get {
        return this._index;
      }
    }
  }

  public interface _IOption<T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_some { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() {
    }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<_IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<_IOption<T>>(Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T some) {
      return new Option_Some<T>(some);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_some {
      get {
        var d = this;
        return ((Option_Some<T>)d)._some;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Option_None<T> : Option<T> {
    public Option_None() : base() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _some;
    public Option_Some(T some) : base() {
      this._some = some;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_some));
    }
    public override bool Equals(object other) {
      var oth = other as Option_Some<T>;
      return oth != null && object.Equals(this._some, oth._some);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._some));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._some);
      s += ")";
      return s;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(uint __source) {
      return true;
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
