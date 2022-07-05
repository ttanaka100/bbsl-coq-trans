import           BBSLSyntax
import           CoqSyntax
import           Data.List.Split
import           Lexer
import           Parser
import           System.Environment

main :: IO ()
main = do
    file:_ <- getArgs
    let name = takeWhile (/= '.') (last (splitOn "/" file))
    text <- readFile file
    case parseBBSL file text of
        Left e   -> error (show e)
        Right bbsl -> case typeSpec bbsl of
            Left err -> print err
            Right sp -> writeFile (name ++ ".v") (make name sp)
