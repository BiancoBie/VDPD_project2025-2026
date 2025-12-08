include "helper.dfy"
  
module {:extern "FileInput"} FileInput {
  import opened Byte
  class {:extern "Reader"} Reader {
    static function {:extern "shouldEncode"} shouldEncode() : bool
    static function {:extern "getContent"} getContent() : array<byte>
    static method {:extern "putContent"} putContent(x : array<byte>, size : uint32)
    static function {:extern "getTimestamp"} getTimestamp() : int
    static function {:extern "getChannels"} getChannels() : byte
    ensures 3 <= getChannels() as int <= 4
  }
}
