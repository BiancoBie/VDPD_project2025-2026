include "helper.dfy"
include "file_input.dfy"
include "qoi.dfy"

import opened Byte

method Main()
{
  var input : array<byte> := FileInput.Reader.getContent();
  if (input.Length < 8)
  {
    print "Invalid input";
  }
  else
  {
    var b := FileInput.Reader.shouldEncode();
    if (b)
    {
      print "Encoding", "\n";
      var width : uint32 := pack(input[0..4]);
      var height : uint32 := pack(input[4..8]);
      var channels : byte := FileInput.Reader.getChannels();
      assert 3<= channels as int <=4;
      print "Width = ", width, "\n";
      print "Height = ", height, "\n";
      print "Channels = ", channels, "\n";
      if (input.Length as int - 8 != width as int * height as int * channels as int)
      {
        print "Invalid input (width * height * channels)";
      }
      else
      {
        var image : Image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
        var s : seq<byte> := encodeAll(image);
        var repeat := 0;
        while (repeat < 0)
          invariant 0 <= repeat <= 0
        {
          //print repeat;
          input := FileInput.Reader.getContent();
          image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
          s := encodeAll(image);
          repeat := repeat + 1;
        }
        var result : array<byte> := new byte [|s|];
        var i := 0;
        while (i < |s|)
          invariant 0 <= i <= |s|
        {
          result[i] := s[i];
          i := i + 1;
        }
        FileInput.Reader.putContent(result);      
      }
    }
    else
    {
      print "Decoding";
      var result : Option<Image> := decodeAll(input[..]);
      var repeat := 0;
      while (repeat < 99999)
        invariant 0 <= repeat <= 100000
      {
        //print repeat;
        var myinput := FileInput.Reader.getContent();
        result := decodeAll(myinput[..]);
        //print result.Some?;
        repeat := repeat + 1;
      }
      if (result.None?)
      {
        print "Invalid encoding";
      }
      else
      {
        var image : Image := result.some;
        var w : uint32 := image.desc.width;
        var h : uint32 := image.desc.height;
        var ws := unpack(w);
        var hs := unpack(h);
        var buffer : array<byte> := new byte [8 + |image.data|];
        buffer[0] := ws[0];
        buffer[1] := ws[1];
        buffer[2] := ws[2];
        buffer[3] := ws[3];
        buffer[4] := hs[0];
        buffer[5] := hs[1];
        buffer[6] := hs[2];
        buffer[7] := hs[3];
        var i : int := 0;
        while (i < |image.data|)
          invariant 0 <= i <= |image.data|
        {
          buffer[8 + i] := image.data[i];
          i := i + 1;
        }
        FileInput.Reader.putContent(buffer);
      }
    }
  }
}