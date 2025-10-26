module Queue where

-- f - forward list
-- r -- reverse list
data Queue a = Queue { f :: [a], r :: [a] } deriving Show

empty :: Queue a -> Bool
empty q =
  case q of
    Queue [] [] -> True
    Queue _ _ -> False

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue q =
  let
    fq = f q
    rq = r q
  in
    case fq of
      [] -> case rq of
        [] -> Nothing
        _ -> let
               rev = reverse rq
               h = head rev
               tl = tail rev
             in
               Just (h, Queue tl [])
      h:ft -> Just (h, Queue ft rq)

enqueue :: a -> Queue a -> Queue a
enqueue a q =
  case q of
    Queue f r -> Queue f (a:r)
