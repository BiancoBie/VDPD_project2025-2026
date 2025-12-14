using System;
using System.Collections;
using System.Text;
using System.IO;

namespace @FileInput {
    public partial class @Reader
    {
        public static bool shouldEncode()
        {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {
                return !argList[1].EndsWith("qoi");
              } else {
                return false;
              }
            }

            return false;
        }

        public static byte getChannels() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1 && File.Exists(argList[1])) {
                byte[] content = System.IO.File.ReadAllBytes(argList[1]);
                
                // Check if it's a QOI file (magic bytes: "qoif")
                if (content.Length >= 14 && 
                    content[0] == 0x71 && content[1] == 0x6f && 
                    content[2] == 0x69 && content[3] == 0x66) {
                    // QOI file format: byte 12 contains the channel count
                    return content[12];
                }
                
                // For raw RGB/RGBA files, check width/height/data size
                if (content.Length >= 8) {
                    //width and height 
                    uint width = ((uint)content[0] << 24) | ((uint)content[1] << 16) | ((uint)content[2] << 8) | (uint)content[3];
                    uint height = ((uint)content[4] << 24) | ((uint)content[5] << 16) | ((uint)content[6] << 8) | (uint)content[7];
                    
                    long dataSize = content.Length - 8;
                    long expectedRGBA = (long)width * height * 4;
                    long expectedRGB = (long)width * height * 3;

                    if (dataSize == expectedRGBA) {
                        return 4; // RGBA
                    } else if (dataSize == expectedRGB) {
                        return 3; // RGB
                    }
                }
            }

            //rgb default
            return 3;
        }

        public static byte[] getContent() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {

                return System.IO.File.ReadAllBytes(argList[1]);
              } else {
                return new byte [0];
              }
            }

            return new byte [0];
        }

        public static void putContent(byte[] contents) {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {
                String suffix;
                if (shouldEncode()) {
                   suffix = ".qoi";
                } else {
                  byte channels = getChannels();
                  suffix = (channels == 4) ? ".rgba" : ".rgb";
                }
                System.IO.File.WriteAllBytes(argList[1] + suffix, contents);
              } else {
                return;
              }
            }

            return;
        }

        public static long getTimestamp() {
          return DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
        }
    }
}
