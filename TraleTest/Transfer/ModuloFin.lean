import Mathlib

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import Trale.Theories.Forall

import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.TrAdvance

open TraleTest.Lemmas

instance : Param40 (Modulo (n + 1)) (Fin (n + 1)) := by
  tr_from_map

  intro a
  constructor

  case val =>
    exact a.repr

  case isLt =>
    simp [Modulo.repr]

    exact smallerThanMod _ _



theorem P1 : ∀ f : (a : Nat) → Fin (a+1),
             ∑ b ∈ {1, 2, 3}, (f b).val ≤ 6
  := by
  simp
  omega

theorem P1' : ∀ f : (a : Nat) → Modulo (a+1),
              ∑ b ∈ {1, 2, 3}, (f b).repr ≤ 6
  := by

  -- apply fun x => Param.right x P1
  -- apply fun x : Param10 _ _ => x.right P1

  tr_by P1

  tr_intro b b' bR
  -- tr_advance
  tr_advance
  tr_advance


  -- let : Param.R _ _ _ _ := by assumption;
  -- let g := this.symm
  -- subst g


  -- tr_whnf at aR




  -- apply_assumption

  tr_advance



  tr_advance
  tr_advance

  tr_advance
  -- (tr_split_application')
  tr_advance

  -- apply_assumption
  -- tr_advance

  funext b
  -- focus show ((?x: (_ : _) -> _) b : Modulo (b+1)).repr = @Fin.val (b+1) ((?x': (_ : _) -> _) b);

  -- let xR : Param.R MapType.Map0 MapType.Map2a (by assumption : (a : ℕ) → Fin (a + 1)) _ = by assumption
  specialize bR b b rfl
  -- dsimp [inferInstance] at bR
  -- tr_whnf at bR
  assumption

  tr_advance
  -- exact (Param44_ident'' rfl).forget

  tr_advance

  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- intro c c' cR
  -- tr_advance
  -- tr_whnf
  -- intro d d' dR
  -- tr_advance
  -- tr_whnf
  -- intro e e' eR
  -- tr_whnf

  -- tr_advance

  -- dsimp
  -- tr_advance


  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- repeat tr_advance

  -- tr_whnf
  -- -- unfold a✝¹









  -- refine (Trale.instantiatePropR_bi ?_).forget


  -- tr_advance
  -- run_tac
  --   trace[tr.utils] s!"Goal is {repr (←Lean.Elab.Tactic.getMainTarget)}"



  -- tr_advance

  -- -- (tr_split_application')
  -- tr_split_application



  -- tr_advance










  -- -- ·
  -- --   let := by assumption
  -- --   funext x y
  -- --   tr_whnf at this


  -- --   subst this
  -- --   simp



  -- -- have h := by assumption
  -- -- rw [h]

  -- run_tac
  --   trace[tr.utils] s!"{←Lean.Elab.Tactic.getMainTarget}"
  --   trace[tr.utils] s!"{repr (←Lean.Elab.Tactic.getMainGoal)}"

  -- -- focus
  -- --   case p2 =>
  -- --     sorry

  -- -- tr_advance

  -- -- · show Param2a0 (Modulo (_ + 1)) (Fin (_ + 1))
  -- --   have := by assumption
  -- --   subst this
  -- --   infer_instance


  -- -- case p2 =>
  -- --   tr_split_application' (allowHead := false)


  -- --   case p1 =>
  -- --     infer_instance

  -- --   case aR =>
  -- --     tr_whnf
  -- --     rfl


  -- --   -- apply refoldMap10
  -- --   rw [←refoldMap10Eq]
  -- --   -- have a := a
  -- --   -- revert a


  -- --   sorry


  -- tr_advance
  -- tr_advance
  -- tr_advance

  -- tr_advance
  -- tr_advance
  -- tr_advance


  -- repeat tr_advance

  -- · show HAdd.hAdd = fun a' => HAdd.hAdd _
  --   funext
  --   apply_assumption
  --   congr




  --   sorry
