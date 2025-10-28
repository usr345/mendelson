module Queue where

-- f - forward list
-- r -- reverse list
-- Добавление производится в reverse, извлечение из forward
data Queue a = Queue { f :: [a], r :: [a] } deriving Show

-- A smart constructor to maintain the invariant.
-- It balances the queue by reversing the back list and moving it to the front
-- when the front list becomes empty.
makeq :: [a] -> [a] -> Queue a
makeq [] b = Queue (reverse b) []
makeq f b = Queue f b

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

-- Get the element at the front of the queue without removing it.
peek :: Queue a -> Maybe a
peek (Queue [] []) = Nothing
peek (Queue (x:_) _) = Just x
