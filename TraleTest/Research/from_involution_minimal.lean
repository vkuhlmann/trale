import Trale.Utils.Basic

def flip_prod : α × β → β × α
  | (a, b) => (b, a)

example : Param44 (α × β) (β × α) :=
  by tr_from_involution flip_prod
