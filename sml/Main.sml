structure Main = struct

open Search

fun int_from_stream stream = Option.valOf (TextIO.scanStream (Int.scan StringCvt.DEC) stream)
val n = int_from_stream TextIO.stdIn
val search = [(Search.print_search, Search.ktp_vars, Search.ktp), (Search.print_search, Search.nspk_vars, Search.nspk), (Search.print_search_slow, Search.ktp_vars, Search.ktp), (Search.print_search_slow, Search.nspk_vars, Search.nspk)]
val out = let val (s, vs, cs) = List.nth (search, n) in s vs cs end
val _ = print (out ^ "\n")

end
