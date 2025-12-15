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
        print "Building image\n";
        var image : Image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
        var result : array<byte>;
        var len : int;
        print "Start encoding\n";
        result, len := encodeAll(image);
        var repeat := 0;
        while (repeat < 99)
          invariant 0 <= repeat <= 99
        {
          print repeat;
          input := FileInput.Reader.getContent();
          image := Image(Desc(width, height, channels as Channels, SRGB), input[8..]);
          result, len := encodeAll(image);
          repeat := repeat + 1;
        }
        //var s : seq<byte> := result[..len];
        //var towrite : array<byte> := new byte [len];
        // var i := 0;
        // while (i < |s|)
        //   invariant 0 <= i <= |s|
        // {
        //   result[i] := s[i];
        //   i := i + 1;
        // }
        // var towrite : array<byte> := new byte [len];
        // assert len >= 0;
         // var i := 0;
         // while (i < len)
         //  invariant 0 <= i <= len
         // {
         //  towrite[i] := result[i];
         //  i := i + 1;
         // }
        if (0 <= len < 4294967296) {
          FileInput.Reader.putContent(result, len as uint32);
        } else {
          print "Error: buffer too big";
        }
      }
    }
    else {
      print "Decoding\n";
      
      // decodeAll returneaza acum (Desc, array<byte>)
      var result : Option<(Desc, array<byte>)> := decodeAll(input);

      if (result.Some?) {
        var desc := result.some.0; // .0 este primul element din tuplu (Desc)
        print "Width = ", desc.width, "\n";
        print "Height = ", desc.height, "\n";
        print "Channels = ", desc.channels, "\n";
      }

      print "Start decoding\n";

      var repeat := 0;
      while repeat < 9
        invariant 0 <= repeat <= 10
      {
        print repeat;
        var myinput := FileInput.Reader.getContent();
        result := decodeAll(myinput);
        repeat := repeat + 1;
      }
      print "\n"; 

      if (result.None?) {
        print "Invalid encoding";
      } else {
        var desc := result.some.0;
        var pixelData := result.some.1; // Acesta este array-ul rapid de bytes!
        
        var w : uint32 := desc.width;
        var h : uint32 := desc.height;
        var ws := unpack(w);
        var hs := unpack(h);
        
        // Cream buffer-ul final (8 bytes header custom + pixel data)
        var buffer : array<byte> := new byte [8 + pixelData.Length];
        
        // Scriem header-ul tau custom pentru output
        buffer[0] := ws[0];
        buffer[1] := ws[1];
        buffer[2] := ws[2];
        buffer[3] := ws[3];
        buffer[4] := hs[0];
        buffer[5] := hs[1];
        buffer[6] := hs[2];
        buffer[7] := hs[3];
        
        var i : int := 0;
        // Aceasta bucla este acum RAPIDA (O(N)) pentru ca lucram array-la-array
        while (i < pixelData.Length)
          invariant 0 <= i <= pixelData.Length
        {
          buffer[8 + i] := pixelData[i];
          i := i + 1;
        }
        
        if (0 <= buffer.Length < 4294967296) {
          FileInput.Reader.putContent(buffer, buffer.Length as uint32);
        } else {
          print "Error: buffer too big";
        }
      }
    }
  }
}