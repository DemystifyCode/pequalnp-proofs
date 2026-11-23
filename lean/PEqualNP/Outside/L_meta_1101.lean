import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1101_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def gates (i k p t : ℕ) : ℕ → List Gate
  | 0 => []
  | j+1 => ⟨.and, [p,i]⟩ :: ⟨.or, [t,k]⟩ :: ⟨.or, [p,i]⟩ ::
      gates (i+1) (k+3) (k+2) (k+1) j

def output (k t : ℕ) : ℕ → ℕ
  | 0 => t
  | j+1 => output (k+3) (k+1) j

theorem gates_length (i k p t j : ℕ) : (gates i k p t j).length = 3*j := by
  induction j generalizing i k p t with
  | zero => rfl
  | succ j ih => simp [gates, ih, Nat.mul_succ]

theorem gates_allowed (i k p t j : ℕ) (g : Gate) (hg : g ∈ gates i k p t j) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  induction j generalizing i k p t with
  | zero => simp [gates] at hg
  | succ j ih =>
    simp only [gates,List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | h
    · exact ⟨Or.inl rfl,le_rfl⟩
    · exact ⟨Or.inr rfl,le_rfl⟩
    · exact ⟨Or.inr rfl,le_rfl⟩
    · exact ih _ _ _ _ h

theorem update_values (w : List Bool) (i k p t : ℕ) (hk : w.length = k)
    (hi : i<k) (hp : p<k) (ht : t<k) :
    step (step (step w ⟨.and,[p,i]⟩) ⟨.or,[t,k]⟩) ⟨.or,[p,i]⟩ =
      w ++ [w.getD p false && w.getD i false,
        w.getD t false || (w.getD p false && w.getD i false),
        w.getD p false || w.getD i false] := by
  subst k
  simp [step,GateOp.eval,List.getElem?_append_left hi,List.getElem?_append_left hp,
    List.getElem?_append_left ht, List.append_assoc]

theorem run_correct (xs : List Bool) (w : List Bool) (i k p t a : ℕ)
    (hk : w.length=k) (hlen : i+xs.length≤k) (hp : p<k) (ht : t<k)
    (hread : ∀ j, j<xs.length → w.getD (i+j) false = xs.getD j false)
    (hany : w.getD p false = decide (1≤a)) (htwo : w.getD t false = decide (2≤a)) :
    ((gates i k p t xs.length).foldl step w).getD (output k t xs.length) false =
      decide (2≤a+xs.count true) := by
  induction xs generalizing w i k p t a with
  | nil => simpa [gates,output] using htwo
  | cons b bs ih =>
    have hi : i<k := by simp at hlen; omega
    have hb : w.getD i false = b := by simpa using hread 0 (by simp)
    let c := if b then 1 else 0
    have hca : (decide (1≤a) || b) = decide (1≤a+c) := by
      cases b <;> simp [c]
    have hct : (decide (2≤a) || (decide (1≤a) && b)) = decide (2≤a+c) := by
      cases b <;> simp [c]
      omega
    have hend : a+(b::bs).count true = (a+c)+bs.count true := by
      cases b <;> simp [c]
      omega
    simp only [List.length_cons,gates,output,List.foldl_cons]
    rw [update_values w i k p t hk hi hp ht, hany,htwo,hb,hend]
    apply ih
    · simp [hk]
    · simp at hlen; omega
    · omega
    · omega
    · intro j hj
      rw [List.getD_append _ _ _ _ (by simp at hlen; omega)]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hread (j+1) (by simp; omega)
    · rw [List.getD_append_right _ _ _ _ (by omega), hk]
      simpa using hca
    · rw [List.getD_append_right _ _ _ _ (by omega), hk]
      simpa using hct

theorem construct (n : ℕ) (hn : 2≤n) :
    ∃ C : Circuit, IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.size ≤ 3*n ∧ ∀ x : List Bool, x.length=n → (C.eval x=true ↔ 2≤x.count true) := by
  let C : Circuit := ⟨⟨.or,[]⟩ :: gates 1 (n+1) 0 n (n-1),output (n+1) n (n-1)⟩
  have hl (g : Gate) (hg : g ∈ C.gates) :
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨Or.inr rfl,by decide⟩
    · exact gates_allowed _ _ _ _ _ _ h
  refine ⟨C,fun g hg => (hl g hg).1,fun g hg => (hl g hg).2,?_,?_⟩
  · simp [C,Circuit.size,gates_length]; omega
  · intro x hx
    cases x with
    | nil => simp at hx; omega
    | cons b bs =>
      have hs : bs.length=n-1 := by simp at hx; omega
      let a := if b then 1 else 0
      have hc := run_correct bs ((b::bs)++[false]) 1 (n+1) 0 n a
        (by simp only [List.length_append,hx]; rfl) (by omega) (by omega) (by omega)
        (by intro j hj; rw [List.getD_append _ _ _ _ (by simp; omega)]
            simp [Nat.add_comm])
        (by cases b <;> simp [a])
        (by rw [List.getD_append_right _ _ _ _ (by omega),hx]; cases b <;> simp [a])
      have he : C.eval (b::bs) = decide (2≤a+bs.count true) := by
        change ((gates 1 (n+1) 0 n (n-1)).foldl step ((b::bs)++[false])).getD
          (output (n+1) n (n-1)) false = _
        rwa [← hs]
      have hcount : a+bs.count true = (b::bs).count true := by
        cases b <;> simp [a,Nat.add_comm]
      simp [he,hcount]

end PEqualNP.Outside.L_meta_1101_aux

theorem PEqualNP.Outside.L_meta_1101 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.size ≤ 3 * n ∧ ∀ x : List Bool, x.length = n → (C.eval x = true ↔ 2 ≤ x.count true) :=
  PEqualNP.Outside.L_meta_1101_aux.construct
