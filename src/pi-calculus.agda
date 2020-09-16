module Pi-Calculus where

-- Local modules ---------------------------------------------------------------

open import Common
     using (Id)
     
-- π-process definition --------------------------------------------------------

data π-process : Set where
   recv_from_∙_ : Id → Id → π-process → π-process       -- Receive
   send_to_∙_   : Id → Id → π-process → π-process       -- Send
   _||_         : π-process → π-process → π-process     -- Composition
   ν_∙_         : Id → π-process → π-process            -- Restriction
   !_           : π-process → π-process                 -- Repetition
   Zero         : π-process                             -- Inactivity
