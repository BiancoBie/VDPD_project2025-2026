/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */
include "spec.dfy"

datatype Option<T> = None | Some(some:T)

module Byte
{
  // standard system unsigned integers
  newtype {:nativeType "byte"} byte = x : int | 0 <= x < 256
  newtype {:nativeType "uint"} uint32 = x : int | 0 <= x < 4294967296
}

import opened Byte

// modular arithmetic
function add_byte(x : byte, y : byte) : byte
{
  ((x as int + y as int) % 256) as byte
}

// modular arithmetic
function sub_byte(x : byte, y : byte) : byte
{
  (((x as int) + (256 - y as int)) % 256) as byte
}

lemma add_sub(x : byte, y : byte)
  ensures sub_byte(add_byte(x, y), y) == x
{
}

function byte_from(x : int) : byte
{
  (x % 256) as byte
}

// uint32 as sequence of 4 bytes
function unpack(x : uint32) : seq<byte>
  ensures |unpack(x)| == 4
{
  var b0 : byte := ((x / (256 * 256 * 256)) % 256) as byte;
  var b1 : byte := ((x / (256 * 256)) % 256) as byte;
  var b2 : byte := ((x / 256) % 256) as byte;
  var b3 : byte := (x % 256) as byte;
  [ b0, b1, b2, b3 ]
}

// 4 bytes as uint32
function pack(x : seq<byte>) : uint32
  requires |x| == 4
{
  (x[0] as uint32) * 16777216 + (x[1] as uint32) * 65536 + (x[2] as uint32) * 256 + (x[3] as uint32)
}

lemma pack_unpack(x : seq<byte>)
  requires |x| == 4
  ensures unpack(pack(x)) == x
{
  assume false;
}

lemma unpack_pack(x : uint32)
  ensures pack(unpack(x)) == x
{
}
    
    
lemma toByteStreamRGBLast(s: seq<RGBA>, x: RGBA)
  ensures toByteStreamRGB(s + [x]) == toByteStreamRGB(s) + [x.r, x.g, x.b]
{
  if |s| == 0 {
    // Cazul de bază este trivial pentru Dafny
  } else {
    // Pasul inductiv
    calc {
      toByteStreamRGB(s + [x]);
      
      // 1. Expandam definitia functiei pentru secventa (s + [x])
      // Dafny stie ca primul element e s[0] si restul e s[1..] + [x]
      { assert (s + [x])[0] == s[0]; }
      { assert (s + [x])[1..] == s[1..] + [x]; }
      [s[0].r, s[0].g, s[0].b] + toByteStreamRGB(s[1..] + [x]);
      
      // 2. Aplicam ipoteza inductiva (apelul recursiv al lemei)
      { toByteStreamRGBLast(s[1..], x); }
      [s[0].r, s[0].g, s[0].b] + (toByteStreamRGB(s[1..]) + [x.r, x.g, x.b]);
      
      // 3. Folosim proprietatea de asociativitate a secventelor: (A + B) + C == A + (B + C)
      ([s[0].r, s[0].g, s[0].b] + toByteStreamRGB(s[1..])) + [x.r, x.g, x.b];
      
      // 4. Recunoastem definitia functiei pentru s
      toByteStreamRGB(s) + [x.r, x.g, x.b];
    }
  }
}

lemma toByteStreamRGBALast(s: seq<RGBA>, x: RGBA)
  ensures toByteStreamRGBA(s + [x]) == toByteStreamRGBA(s) + [x.r, x.g, x.b, x.a]
{
  if |s| == 0 {
  } else {
    calc {
      toByteStreamRGBA(s + [x]);
      
      { assert (s + [x])[0] == s[0]; }
      { assert (s + [x])[1..] == s[1..] + [x]; }
      [s[0].r, s[0].g, s[0].b, s[0].a] + toByteStreamRGBA(s[1..] + [x]);
      
      { toByteStreamRGBALast(s[1..], x); }
      [s[0].r, s[0].g, s[0].b, s[0].a] + (toByteStreamRGBA(s[1..]) + [x.r, x.g, x.b, x.a]);
      
      ([s[0].r, s[0].g, s[0].b, s[0].a] + toByteStreamRGBA(s[1..])) + [x.r, x.g, x.b, x.a];
      
      toByteStreamRGBA(s) + [x.r, x.g, x.b, x.a];
    }
  }
}

  

  
