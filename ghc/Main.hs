import qualified Search

main = do
    l <- getLine
    let search = [Search.print_search_KTP, Search.print_search_NSPK, Search.print_search_slow_KTP, Search.print_search_slow_NSPK]
    putStrLn $ search !! (read l)
