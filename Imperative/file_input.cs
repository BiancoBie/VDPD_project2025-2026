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
                
                // MODIFICARE AICI: Verificam intai daca este fisier QOI
                // Header-ul QOI incepe cu "qoif" (bytes: 113, 111, 105, 102)
                if (content.Length >= 14 && 
                    content[0] == 113 && content[1] == 111 && content[2] == 105 && content[3] == 102) {
                    
                    // In specificatia QOI, numarul de canale este la indexul 12
                    return content[12]; 
                }

                // Daca nu e QOI, folosim logica veche pentru fisiere RAW
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

        public static void putContent(byte[] contents, uint size) {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {
                String inputFilename = argList[1];
                String outputFilename;
                
                if (shouldEncode()) {
                   // La encoding adaugam .qoi
                   outputFilename = inputFilename + ".qoi";
                } else {
                  // La decoding, determinam extensia corecta
                  byte channels = getChannels();
                  String extension = (channels == 4) ? ".rgba" : ".rgb";
                  
                  // MODIFICARE OPTIONALA: Pentru a evita input.rgba.qoi.rgb
                  // Daca fisierul se termina in .qoi, il scoatem inainte sa punem extensia noua
                  if (inputFilename.EndsWith(".qoi")) {
                      outputFilename = inputFilename.Substring(0, inputFilename.Length - 4) + ".decoded" + extension;
                  } else {
                      outputFilename = inputFilename + extension;
                  }
                }
                
                byte [] towrite = new byte [size];
                Array.Copy(contents, 0, towrite, 0, size);
                
                // Scriem in noul nume de fisier calculat
                System.IO.File.WriteAllBytes(outputFilename, towrite);
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