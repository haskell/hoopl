module Rew
where

data Rew a = No
           | Mk a
           | Then (Rew a) (Rew a)
           | Iter (Rew a)

rewrite :: Rew (node -> fact -> Maybe graph)
        -> node -> fact -> Maybe (graph, Rew (node -> fact -> Maybe graph))
rewrite_direct rs n f = rew rs
    where rew No       = Nothing
          rew (Mk r)   =
              case r n f of Nothing -> Nothing
                            Just g -> Just (g, No)
          rew (r1 `Then` r2) =
              case rew r1 of
                Nothing -> rew r2
                Just (g, r1') -> Just (g, r1' `Then` r2)
          rew (Iter r) =
              case rew r of
                Nothing -> Nothing
                Just (g, r') -> Just (g, r' `Then` Iter r)

rewrite rs node f = rew rs Just Nothing
 where
  rew No     j n = n
  rew (Mk r) j n =
     case r node f of Nothing -> n
                      Just g -> j (g, No)
  rew (r1 `Then` r2) j n = rew r1 (j . add r2) (rew r2 j n)
  rew (Iter r)       j n = rew r (j . add (Iter r)) n
  add tail (g, r) = (g, r `Then` tail)

rewritem :: Monad m => Rew (node -> fact -> m (Maybe graph))
         -> node -> fact -> m (Maybe (graph, Rew (node -> fact -> m (Maybe graph))))
rewritem rs node f = rew rs (return . Just) (return Nothing)
 where
  rew No     j n = n
  rew (Mk r) j n = do mg <- r node f
                      case mg of Nothing -> n
                                 Just g -> j (g, No)
  rew (r1 `Then` r2) j n = rew r1 (j . add r2) (rew r2 j n)
  rew (Iter r)       j n = rew r (j . add (Iter r)) n
  add tail (g, r) = (g, r `Then` tail)

