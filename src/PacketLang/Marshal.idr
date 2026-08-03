module PacketLang.Marshal

import PacketLang.DSL
import PacketLang.BitLength

public export
Position : Type
Position = Offset

-- Binary + Offset replacing ActivePacket
covering public export
unmarshal' : Binary -> Position -> (pl : PacketLang) -> Maybe (mkTy pl, Length)
unmarshal' b w pl =
    let
        (w', res) = parse ddc b w
        Yes _ = res.ec `decEq` OK
            | No _ => Nothing
        rep = stripMetadata ddc res
    in
        Just (rep, w')
    where
        ddc = toDDC pl

-- Binary replacing BufPtr + Length
covering public export
unmarshal :
    (pl : PacketLang) -> 
    Binary ->
    Maybe (mkTy pl, Length) -- TODO: ByteLength?
unmarshal pl b = unmarshal' b 0 pl

-- Binary replacing IO (BufPtr, Length)
public export
marshal : (pl : PacketLang) -> (mkTy pl) -> Binary
marshal pl = serialise (toDDC pl)
