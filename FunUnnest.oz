functor
import
   \insert CP-new.env
   \insert Misc-new.env
   FlattenSequence
   Core
   Gump.{transformParser transformScanner}
export
   JoinQueries
   MakeExpressionQuery
   UnnestQuery
body
   \insert TupleSyntax
   \insert BindingAnalysis
   \insert UnnestFD
in
   \insert Unnester
end