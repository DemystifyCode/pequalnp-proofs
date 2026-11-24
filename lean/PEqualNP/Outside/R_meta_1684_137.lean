import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Native list and gate equations adapt L_meta_1491.S90 (7328b43b).
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1684_137
    (cleanCost :
let ds : Finset (Fin 13) := {0, 1, 3, 9}
let I := fun p l : Fin 13 => p - l ∈ ds
let edge := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
  I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
  (∀ x, PEqualNP.MetaComplexity.circuitFun 26 C x = true ↔ edge x) →
  (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x,
    PEqualNP.EdgeOwnership.gateVal 26 C j x = true → edge x) →
  64 ≤ C.size)
    (dirtyCost :
let ds : Finset (Fin 13) := {0, 1, 3, 9}
let I := fun p l : Fin 13 => p - l ∈ ds
let ok := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
  (∀ p l, I p l → PEqualNP.MetaComplexity.circuitFun 26 C
    (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = true) ∧
  (∀ P : Finset (Fin 13),
    let T := Finset.univ.filter (fun l => ∀ p ∈ P, p - l ∉ ds)
    (∀ p ∉ P, ∃ l ∈ T, I p l) →
    (∃ a : Fin 13, (∀ p ∈ P, I p a) ∨ (∀ l ∈ T, I a l)) →
    PEqualNP.MetaComplexity.circuitFun 26 C (Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ T))) = false)
let lost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) =>
  let S : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e => e.1 - e.2 ∈ ds ∧
    PEqualNP.MetaComplexity.circuitFun 26 {C with gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩}
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 e.1) (Fin.natAdd 13 e.2)) = false
  S.card
let edge := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
  I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
∀ C, PEqualNP.MetaComplexity.Monotone2 C → ok C →
  (∃ (j : ℕ) (u v : Fin 26), PEqualNP.EdgeOwnership.Owns 26 C j u v ∧
    ¬ edge (PEqualNP.EdgeOwnership.pairInput u v) ∧ 2 ≤ lost C j) → 64 ≤ C.size)
    : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have pairInput_bits {n : Nat} (a b i : Fin n) :
      pairInput a b i = decide (i = a ∨ i = b) := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp only [eval_or, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp only [eval_and, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; cases h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2

  have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]

  have gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
      PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

  let act {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) := val C (List.ofFn x) i

  let sufficientLiteral {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Prop :=
    ∃ a : Fin n, x a = true ∧ ∀ y : Fin n → Bool, y a = true → act C y i = true

  have two_literals {n : ℕ} {C : Circuit} {x : Fin n → Bool}
      (d : Fin n) (neg : Fin n → Fin n → Prop) (hd : neg d d)
      (hx : ∀ a b, x a = true → x b = true → neg a b)
      (l : List ℕ) (hl : l.length ≤ 2)
      (h : ∀ i ∈ l, sufficientLiteral C x i) :
      ∃ a b, neg a b ∧ ∀ i ∈ l, act C (pairInput a b) i = true := by
    cases l with
    | nil => exact ⟨d, d, hd, by simp⟩
    | cons i l =>
      obtain ⟨a, ha, Fa⟩ := h i (by simp)
      cases l with
      | nil =>
        refine ⟨a, a, hx a a ha ha, ?_⟩
        simpa using Fa (pairInput a a) (by simp [pairInput_bits])
      | cons j l =>
        obtain ⟨b, hb, Fb⟩ := h j (by simp)
        cases l with
        | nil =>
          refine ⟨a, b, hx a b ha hb, ?_⟩
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact Fa _ (by simp [pairInput_bits])
          · exact Fb _ (by simp [pairInput_bits])
        | cons k t => simp at hl

  have and_contradiction {n : ℕ} {C : Circuit} {x : Fin n → Bool}
      (d : Fin n) (neg : Fin n → Fin n → Prop) (hd : neg d d)
      (hx : ∀ a b, x a = true → x b = true → neg a b)
      (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
      (hand : (gateAt C j).op = .and)
      (hclean : ∀ a b, neg a b → gateVal n C j (pairInput a b) = false)
      (previous : ∀ i < n + j, act C x i = true → sufficientLiteral C x i)
      (hv : act C x (n+j) = true) : False := by
    have hon := (val_and (n := n) (by simp) hj hand).mp hv
    obtain ⟨a,b,hab,hp⟩ := two_literals d neg hd hx _ (hm _ (gateAt_mem hj)).2
      (fun i hi => previous i (hon i hi).1 (hon i hi).2)
    have ht : gateVal n C j (pairInput a b) = true :=
      (val_and (n := n) (by simp) hj hand).mpr (fun i hi => ⟨(hon i hi).1,hp i hi⟩)
    rw [hclean _ _ hab] at ht
    cases ht

  have wire_literal {n : ℕ} {C : Circuit} {x : Fin n → Bool}
      (d : Fin n) (neg : Fin n → Fin n → Prop) (hd : neg d d)
      (hx : ∀ a b, x a = true → x b = true → neg a b)
      (hm : Monotone2 C)
      (hclean : ∀ j < C.gates.length, (gateAt C j).op = .and →
        ∀ a b, neg a b → gateVal n C j (pairInput a b) = false) :
      ∀ i, act C x i = true → sufficientLiteral C x i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hv
      by_cases hi : i < n
      · let a : Fin n := ⟨i, hi⟩
        refine ⟨a, (val_ofFn C x a).symm.trans hv, ?_⟩
        intro y hy
        exact (val_ofFn C y a).trans hy
      by_cases ho : n + C.gates.length ≤ i
      · rw [show act C x i = false from val_ge (by simp) ho] at hv
        cases hv
      obtain ⟨j, rfl⟩ : ∃ j, i = n+j := ⟨i-n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := (hm _ (gateAt_mem hj)).1
      rcases hop with ha | hor
      · exact (and_contradiction d neg hd hx hm j hj ha (hclean j hj ha) ih hv).elim
      · obtain ⟨w, hw, hlt, ht⟩ := (val_or (n := n) (by simp) hj hor).mp hv
        obtain ⟨a, hxa, ja⟩ := ih w hlt ht
        refine ⟨a, hxa, fun y hy => ?_⟩
        exact (val_or (n := n) (by simp) hj hor).mpr ⟨w, hw, hlt, ja y hy⟩

  have no_owner_false {n : ℕ} {C : Circuit} {a b : Fin n}
      (hn : ¬ ∃ j, Owns n C j a b) :
      ∀ j < C.gates.length, (gateAt C j).op = .and →
        gateVal n C j (pairInput a b) = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj ha
      cases h : gateVal n C j (pairInput a b) with
      | false => rfl
      | true =>
        exact (hn ⟨j, hj, ha, h, fun i hij _ hi => ih i hij (by omega) hi⟩).elim

  have independent_rejected {n : ℕ} (d : Fin n) (C : Circuit) (hm : Monotone2 C)
      (neg : Fin n → Fin n → Prop) (hd : neg d d)
      (hno : ∀ a b, neg a b → ¬ ∃ j, Owns n C j a b)
      (hdiag : ∀ a, circuitFun n C (pairInput a a) = false)
      (x : Fin n → Bool) (hx : ∀ a b, x a = true → x b = true → neg a b) :
      circuitFun n C x = false ∧
      ∀ j < C.gates.length, (gateAt C j).op = .and → gateVal n C j x = false := by
    have clean : ∀ j < C.gates.length, (gateAt C j).op = .and →
        ∀ a b, neg a b → gateVal n C j (pairInput a b) = false :=
      fun j hj ha a b hab => no_owner_false (hno a b hab) j hj ha
    have lits := wire_literal d neg hd hx hm clean
    constructor
    · cases hout : circuitFun n C x with
      | false => rfl
      | true =>
        obtain ⟨a, _, hl⟩ := lits C.output hout
        have hh : circuitFun n C (pairInput a a) = true := hl _ (by simp [pairInput_bits])
        rw [hdiag] at hh
        cases hh
    · intro j hj ha
      cases hg : gateVal n C j x with
      | false => rfl
      | true =>
        exact (and_contradiction d neg hd hx hm j hj ha (clean j hj ha)
          (fun i _ => lits i) hg).elim
  let I (p l : Fin 13) : Prop := p-l ∈ ({0,1,3,9} : Finset (Fin 13))

  let edge (x : Fin 26 → Bool) : Prop :=
    ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

  let exterior (P : Finset (Fin 13)) : Finset (Fin 13) :=
    Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)

  let row (P : Finset (Fin 13)) : Fin 26 → Bool :=
    Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ exterior P))

  let ok (C : Circuit) : Prop :=
    (∀ p l, I p l → circuitFun 26 C (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = true) ∧
    (∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l ∈ exterior P, I p l) →
      (∃ a : Fin 13, (∀ p ∈ P, I p a) ∨ (∀ l ∈ exterior P, I a l)) →
      circuitFun 26 C (row P) = false)

  have wire_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
      (hxy : ∀ a, x a = true → y a = true) :
      ∀ w, act C x w = true → act C y w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hraw : w < n
      · let a : Fin n := ⟨w,hraw⟩
        exact (val_ofFn C y a).trans (hxy a ((val_ofFn C x a).symm.trans hv))
      by_cases hfar : n + C.gates.length ≤ w
      · have h := val_ge (C := C) (x := List.ofFn x) (by simp) hfar
        exact (Bool.noConfusion (h.symm.trans hv))
      obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := (hm _ (gateAt_mem hj)).1
      rcases hop with ha | hor
      · have h := (val_and (n := n) (by simp) hj ha).mp hv
        apply (val_and (n := n) (by simp) hj ha).mpr
        intro i hi
        obtain ⟨hlt, ht⟩ := h i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (n := n) (by simp) hj hor).mp hv
        exact (val_or (n := n) (by simp) hj hor).mpr ⟨i, hi, hlt, ih i hlt ht⟩

  have diagonal_inc (p : Fin 13) : I p p := by simp [I]
  have exterior_empty : exterior ∅ = Finset.univ := by simp [exterior]
  have exterior_univ : exterior Finset.univ = ∅ := by
    ext l
    simp only [exterior, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    intro h
    exact h l (by simp) (diagonal_inc l)

  have pair_le {n} {a b : Fin n} {x : Fin n → Bool}
      (ha : x a = true) (hb : x b = true) :
      ∀ i, pairInput a b i = true → x i = true := by
    intro i hi
    simp [pairInput_bits] at hi
    rcases hi with rfl | rfl <;> assumption

  have rejects_singletons (C : Circuit) (hm : Monotone2 C) (hc : ok C) :
      ∀ a : Fin 26, circuitFun 26 C (pairInput a a) = false := by
    have bound (P : Finset (Fin 13)) (hf : circuitFun 26 C (row P) = false)
        (a : Fin 26) (h : row P a = true) :
        circuitFun 26 C (pairInput a a) = false := by
      cases hval : circuitFun 26 C (pairInput a a) with
      | false => rfl
      | true =>
        have hv : circuitFun 26 C (row P) = true :=
          wire_mono C hm _ _ (pair_le h h) C.output hval
        rw [hf] at hv
        cases hv
    have h0 : circuitFun 26 C (row ∅) = false := hc.2 ∅
      (fun p _ => ⟨p, by simp [exterior_empty], diagonal_inc p⟩)
      ⟨0, Or.inl (by simp)⟩
    have h1 : circuitFun 26 C (row Finset.univ) = false := hc.2 Finset.univ
      (by simp) ⟨0, Or.inr (by simp [exterior_univ])⟩
    intro a
    refine Fin.addCases (m := 13) (n := 13) (motive := fun a => circuitFun 26 C (pairInput a a) = false) (fun p => ?_) (fun l => ?_) a
    · exact bound _ h1 _ (by simp [row])
    · apply bound _ h0 (Fin.natAdd 13 l)
      dsimp only [row]
      rw [Fin.append_right, exterior_empty]
      simp

  have clean_transfer (C : Circuit) (hm : Monotone2 C) (hc : ok C)
      (ho : ∀ a b : Fin 26, ¬edge (pairInput a b) → ¬∃ j, Owns 26 C j a b) :
      (∀ x, circuitFun 26 C x = true ↔ edge x) ∧
        (∀ j < C.size, (gateAt C j).op = .and → ∀ x, gateVal 26 C j x = true → edge x) := by
    have hpos (x : Fin 26 → Bool) (he : edge x) : circuitFun 26 C x = true := by
      obtain ⟨p,l,hpl,hp,hl⟩ := he
      exact wire_mono C hm _ _ (pair_le hp hl) C.output (hc.1 p l hpl)
    have hz (x : Fin 26 → Bool) (hx : ¬edge x) := independent_rejected
      (0 : Fin 26) C hm (fun a b => ¬edge (pairInput a b))
      (by unfold edge I; decide +kernel) ho (rejects_singletons C hm hc) x (by
        intro a b ha hb he
        obtain ⟨p,l,hi,hp,hl⟩ := he
        exact hx ⟨p,l,hi,pair_le ha hb _ hp,pair_le ha hb _ hl⟩)
    constructor
    · intro x
      refine ⟨?_, hpos x⟩
      intro ht
      by_contra h
      rw [(hz x h).1] at ht
      cases ht
    · intro j hj hop x ht
      by_contra h
      rw [(hz x h).2 j hj hop] at ht
      cases ht
  let replace (C : Circuit) (s : ℕ) (g : Gate) : Circuit := {C with gates := C.gates.set s g}
  let zeroSlot (C : Circuit) (s : ℕ) := replace C s ⟨.or, []⟩
  let edgeSlot {n : ℕ} (C : Circuit) (s : ℕ) (a b : Fin n) :=
    replace C s ⟨.and,[a.val,b.val]⟩

  have replace_length (C : Circuit) (s : ℕ) (g : Gate) :
      (replace C s g).gates.length = C.gates.length := List.length_set

  have at_replace (C : Circuit) (s : ℕ) (g : Gate) (hs : s < C.gates.length) :
      gateAt (replace C s g) s = g := by
    rw [gateAt_eq (by simpa [replace] using hs)]
    simp [replace]

  have at_else (C : Circuit) (s : ℕ) (g : Gate) (j : ℕ)
      (hj : j < C.gates.length) (hjs : j ≠ s) :
      gateAt (replace C s g) j = gateAt C j := by
    rw [gateAt_eq (by simpa [replace] using hj), gateAt_eq hj]
    simp [replace, Ne.symm hjs]

  have replace_mono (C : Circuit) (hc : Monotone2 C) (s : ℕ) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      Monotone2 (replace C s g) := by
    intro k hk
    obtain ⟨i,hi,hki⟩ := List.mem_iff_getElem.mp hk
    have hi' : i < C.gates.length := by simpa [replace] using hi
    rw [← hki, ← gateAt_eq hi]
    by_cases he : i = s
    · subst i
      rw [at_replace C s g hi']
      exact hg
    · rw [at_else C s g _ hi' he]
      exact hc _ (gateAt_mem hi')

  have one_slot {n : ℕ} {C D : Circuit} (hm : Monotone2 C) (s : ℕ)
      (hlen : C.gates.length = D.gates.length)
      (heq : ∀ j < C.gates.length, j ≠ s → gateAt C j = gateAt D j)
      (x : Fin n → Bool) (hc : gateVal n C s x = true → gateVal n D s x = true) :
      ∀ i, act C x i = true → act D x i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hv
      by_cases hi : i < n
      · let t : Fin n := ⟨i,hi⟩
        exact (val_ofFn D x t).trans ((val_ofFn C x t).symm.trans hv)
      by_cases hfar : n + C.gates.length ≤ i
      · have h : act C x i = false := val_ge (by simp) hfar
        rw [h] at hv
        cases hv
      obtain ⟨j,rfl⟩ : ∃ j, i=n+j := ⟨i-n,by omega⟩
      have hj : j < C.gates.length := by omega
      have hj' : j < D.gates.length := hlen ▸ hj
      by_cases he : j=s
      · subst j; exact hc hv
      have eqg := heq j hj he
      have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := (hm _ (gateAt_mem hj)).1
      rcases hop with ha | hor
      · have h := (val_and (n := n) (by simp) hj ha).mp hv
        apply (val_and (n := n) (by simp) hj' (eqg ▸ ha)).mpr
        intro i hi
        obtain ⟨hlt, ht⟩ := h i (eqg.symm ▸ hi)
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (n := n) (by simp) hj hor).mp hv
        apply (val_or (n := n) (by simp) hj' (eqg ▸ hor)).mpr
        exact ⟨i, eqg ▸ hi, hlt, ih i hlt ht⟩

  have zero_value {n : ℕ} (C : Circuit) (s : ℕ) (hs : s < C.gates.length) (x : Fin n → Bool) :
      gateVal n (zeroSlot C s) s x = false := by
    rw [gateVal_eq_val, val_gate (n := n) (by simp)
      (C := zeroSlot C s) (by simpa [zeroSlot, replace] using hs)]
    dsimp only [zeroSlot]
    rw [at_replace C s _ hs]
    rfl

  have edge_value {n : ℕ} (C : Circuit) (s : ℕ) (hs : s < C.gates.length)
      (a b : Fin n) (x : Fin n → Bool) :
      gateVal n (edgeSlot C s a b) s x = true ↔ x a = true ∧ x b = true := by
    rw [gateVal_eq_val]
    have hslot : gateAt (edgeSlot C s a b) s = ⟨.and,[a.val,b.val]⟩ := at_replace _ _ _ hs
    have hr : s < (edgeSlot C s a b).gates.length := by simpa [edgeSlot,replace] using hs
    rw [val_and (n := n) (by simp) hr (by rw [hslot])]
    rw [hslot]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      exact ⟨(val_ofFn _ x a).symm.trans (h _ (Or.inl rfl)).2,
        (val_ofFn _ x b).symm.trans (h _ (Or.inr rfl)).2⟩
    · rintro ⟨ha,hb⟩ i (rfl|rfl)
      · exact ⟨by omega, (val_ofFn _ x a).trans ha⟩
      · exact ⟨by omega, (val_ofFn _ x b).trans hb⟩

  have replace_le {n : ℕ} (C : Circuit) (s : ℕ) (g : Gate) (hm : Monotone2 (replace C s g))
      (x : Fin n → Bool) (hle : gateVal n (replace C s g) s x = true → gateVal n C s x = true) :
      ∀ w, act (replace C s g) x w = true → act C x w = true :=
    one_slot hm s (replace_length C s g)
      (fun j hj hjs => at_else C s g j (by simpa [replace] using hj) hjs) x hle

  have le_replace {n : ℕ} (C : Circuit) (s : ℕ) (g : Gate) (hm : Monotone2 C)
      (x : Fin n → Bool) (hle : gateVal n C s x = true → gateVal n (replace C s g) s x = true) :
      ∀ w, act C x w = true → act (replace C s g) x w = true :=
    one_slot hm s (replace_length C s g).symm (fun j hj hjs => (at_else C s g j hj hjs).symm) x hle

  have zero_le_edge {n : ℕ} (C : Circuit) (hm : Monotone2 C) (s : ℕ) (hs : s < C.gates.length)
      (a b : Fin n) (x : Fin n → Bool) :
      ∀ w, act (zeroSlot C s) x w = true → act (edgeSlot C s a b) x w = true := by
    have hm0 : Monotone2 (zeroSlot C s) :=
      replace_mono C hm s _ ⟨Or.inr rfl,by decide⟩
    apply one_slot hm0 s (by simp [zeroSlot,edgeSlot,replace])
    · intro j hj hjs
      have hj' : j < C.gates.length := by simpa [zeroSlot,replace] using hj
      exact (at_else C s _ j hj' hjs).trans (at_else C s _ j hj' hjs).symm
    · intro hv
      rw [zero_value C s hs x] at hv
      cases hv
  let flag (p l : Fin 13) : Fin 26 → Bool := pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)
  let lost (C : Circuit) (j : ℕ) (p l : Fin 13) :=
    I p l ∧ circuitFun 26 (zeroSlot C j) (flag p l) = false
  let two (C : Circuit) (j : ℕ) := ∃ p l p' l' : Fin 13,
    (p,l) ≠ (p',l') ∧ lost C j p l ∧ lost C j p' l'

  let leaks (C : Circuit) (j : ℕ) := ∃ a b : Fin 26,
    ¬edge (pairInput a b) ∧ gateVal 26 C j (pairInput a b) = true

  let leakingSites (C : Circuit) : Finset ℕ := by
    classical
    exact (Finset.range C.size).filter (leaks C)

  have mem_leakingSites {C : Circuit} {j : ℕ} :
      j ∈ leakingSites C ↔ j < C.size ∧ leaks C j := by classical simp [leakingSites]

  have row_negative (P : Finset (Fin 13)) : ¬edge (row P) := by
    rintro ⟨p,l,hpl,hp,hl⟩
    have h1 : p ∈ P := by simpa [row] using hp
    dsimp only [row] at hl
    rw [Fin.append_right] at hl
    have h2 : l ∈ exterior P := of_decide_eq_true hl
    exact (Finset.mem_filter.mp h2).2 p h1 hpl

  have improve (C : Circuit) (hm : Monotone2 C) (hok : ok C) (j : ℕ)
      (hj : j < C.size) (hleak : leaks C j) (p l : Fin 13) (hpl : I p l)
      (hcover : ∀ a b, lost C j a b → (a,b) = (p,l)) :
      ∃ D : Circuit, Monotone2 D ∧ ok D ∧ D.size = C.size ∧ leakingSites D ⊂ leakingSites C := by
    classical
    let u := Fin.castAdd 13 p
    let v := Fin.natAdd 13 l
    let D := edgeSlot C j u v
    have dm : Monotone2 D := replace_mono C hm j _ ⟨Or.inl rfl,le_rfl⟩
    have deq : D.size = C.size := replace_length C j _
    have hfalse (x : Fin 26 → Bool) (hx : ¬edge x) :
        gateVal 26 D j x = false := by
      cases h : gateVal 26 D j x with
      | false => rfl
      | true =>
        obtain ⟨hu,hv⟩ := (edge_value C j hj u v x).mp h
        exact (hx ⟨p,l,hpl,hu,hv⟩).elim
    have hneg (x : Fin 26 → Bool) (hx : ¬edge x) :
        ∀ w, act D x w = true → act C x w = true :=
      replace_le C j _ dm x (fun ht => by
        have hf := hfalse x hx
        change gateVal 26 D j x = true at ht
        rw [hf] at ht
        cases ht)
    have hgood : ok D := by
      constructor
      · intro a b hab
        cases h0 : circuitFun 26 (zeroSlot C j) (flag a b) with
        | true => exact zero_le_edge C hm j hj u v (flag a b) C.output h0
        | false =>
          have heq := hcover a b ⟨hab,h0⟩
          have hap : a = p := congrArg Prod.fst heq
          have hbl : b = l := congrArg Prod.snd heq
          subst a
          subst b
          have h1 : gateVal 26 D j (flag p l) = true :=
            (edge_value C j hj _ _ _).mpr ⟨by simp [u,flag,pairInput_bits],by simp [v,flag,pairInput_bits]⟩
          exact le_replace C j _ hm (flag p l) (fun _ => h1) C.output (hok.1 p l hab)
      · intro P hmax hdeg
        have h0 := hok.2 P hmax hdeg
        cases hD : circuitFun 26 D (row P) with
        | false => rfl
        | true =>
          have h1 : circuitFun 26 C (row P) = true := hneg _ (row_negative P) C.output hD
          rw [h0] at h1
          cases h1
    have hsub : leakingSites D ⊆ leakingSites C := by
      intro i hi
      obtain ⟨hlim,a,b,hx,ht⟩ := mem_leakingSites.mp hi
      exact mem_leakingSites.mpr ⟨deq ▸ hlim,a,b,hx,hneg _ hx (26+i) ht⟩
    have hmiss : j ∉ leakingSites D := by
      intro h
      obtain ⟨_,a,b,hx,ht⟩ := mem_leakingSites.mp h
      rw [hfalse _ hx] at ht
      cases ht
    refine ⟨D,dm,hgood,deq,Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩⟩
    intro heq
    rw [heq] at hmiss
    exact hmiss (mem_leakingSites.mpr ⟨hj,hleak⟩)

  let minimumScore (C : Circuit) : Prop :=
    ∀ D : Circuit, Monotone2 D → ok D → D.size = C.size →
      (leakingSites C).card ≤ (leakingSites D).card

  have two_of_leaks (C : Circuit) (hm : Monotone2 C) (hC : ok C) (hmin : minimumScore C)
      (j : ℕ) (hj : j < C.size) (hd : leaks C j) : two C j := by
    classical
    by_contra h
    obtain ⟨p,l,hpl,hone⟩ : ∃ p l, I p l ∧ ∀ a b, lost C j a b → (a,b) = (p,l) := by
      by_cases hh : ∃ p l, lost C j p l
      · obtain ⟨p,l,h0⟩ := hh
        refine ⟨p,l,h0.1,?_⟩
        intro a b hab
        by_contra hne
        exact h ⟨a,b,p,l,hne,hab,h0⟩
      · exact ⟨0,0,by simp [I],fun a b hab => (hh ⟨a,b,hab⟩).elim⟩
    obtain ⟨D,hmD,hD,hs,hl⟩ := improve C hm hC j hj hd p l hpl hone
    exact (Nat.not_lt_of_ge (hmin D hmD hD hs)) (Finset.card_lt_card hl)

  have choose_minimumScore (C : Circuit) (hm : Monotone2 C) (hC : ok C) :
      ∃ D : Circuit, Monotone2 D ∧ ok D ∧ D.size = C.size ∧ minimumScore D := by
    classical
    let has (s : ℕ) := ∃ D : Circuit, Monotone2 D ∧ ok D ∧ D.size = C.size ∧ (leakingSites D).card = s
    have yes : ∃ s, has s := ⟨_,C,hm,hC,rfl,rfl⟩
    obtain ⟨D,hmD,hD,hsize,hscore⟩ := Nat.find_spec yes
    refine ⟨D,hmD,hD,hsize,?_⟩
    intro E hmE hE hs
    rw [hscore]
    apply Nat.find_min' yes
    exact ⟨E,hmE,hE,hs.trans hsize,rfl⟩
  let originalTests (C : Circuit) : Prop :=
    (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)

  let inc (p l : Fin 13) : Prop :=
    ∃ dd ∈ ({0,1,3,9} : Finset (Fin 13)), p = l + dd

  have offset : ∀ p l : Fin 13, inc p l ↔ I p l := by dsimp only [inc,I]; decide +kernel

  let misses (P : Finset (Fin 13)) (l : Fin 13) : Prop := ∀ p ∈ P, ¬inc p l

  have misses_iff (P : Finset (Fin 13)) (l : Fin 13) :
      misses P l ↔ l ∈ exterior P := by
    simp only [misses,exterior,Finset.mem_filter,Finset.mem_univ,true_and,offset]

  let maximal (P : Finset (Fin 13)) : Prop :=
    ∀ v ∉ P, ∃ w, misses P w ∧ inc v w

  let degenerate (P : Finset (Fin 13)) : Prop :=
    (∃ l, ∀ p ∈ P, inc p l) ∨ (∃ p, ∀ l, misses P l → inc p l)

  have maximal_iff (P : Finset (Fin 13)) :
      maximal P ↔ ∀ v ∉ P, ∃ l ∈ exterior P, I v l := by
    simp only [maximal,misses_iff,offset]

  have degenerate_iff (P : Finset (Fin 13)) :
      degenerate P ↔ ∃ a, (∀ p ∈ P, I p a) ∨ (∀ l ∈ exterior P, I a l) := by
    simp only [degenerate,misses_iff,offset]
    constructor
    · rintro (⟨l,h⟩ | ⟨p,h⟩)
      · exact ⟨l,Or.inl h⟩
      · exact ⟨p,Or.inr h⟩
    · rintro ⟨a,h | h⟩
      · exact Or.inl ⟨a,h⟩
      · exact Or.inr ⟨a,h⟩

  let originalRow (P : Finset (Fin 13)) (i : Fin 26) : Bool :=
    decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
      (∃ l : Fin 13, i = Fin.natAdd 13 l ∧ misses P l))

  have separate : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide +kernel
  have pin_left : ∀ p q : Fin 13, Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p = q := by decide +kernel
  have pin_right : ∀ p q : Fin 13, Fin.natAdd 13 p = Fin.natAdd 13 q ↔ p = q := by decide +kernel

  have row_eq (P : Finset (Fin 13)) : originalRow P = row P := by
    funext i
    refine Fin.addCases (m := 13) (n := 13) (motive := fun j => originalRow P j = row P j)
      (fun p => ?_) (fun l => ?_) i
    · dsimp only [row]
      rw [Fin.append_left,Bool.eq_iff_iff]
      simp only [originalRow,decide_eq_true_eq,pin_left,separate,false_and,exists_false,or_false]
      exact ⟨fun ⟨q,hq,he⟩ => he.symm ▸ hq, fun hp => ⟨p,hp,rfl⟩⟩
    · have sep (p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := Ne.symm (separate p l)
      dsimp only [row]
      rw [Fin.append_right,Bool.eq_iff_iff]
      simp only [originalRow,decide_eq_true_eq,pin_right,sep,and_false,exists_false,false_or,misses_iff]
      exact ⟨fun ⟨w,he,hw⟩ => he.symm ▸ hw, fun hl => ⟨l,rfl,hl⟩⟩

  have originalTests_iff (C : Circuit) : originalTests C ↔ ok C := by
    conv_rhs =>
      unfold ok
      simp only [← maximal_iff, ← degenerate_iff, ← row_eq]
      simp only [← offset]
    unfold originalTests maximal degenerate originalRow misses inc
    rfl
  classical
  rintro ⟨C, hm, hs, pos, negs⟩
  have good : ok C := (originalTests_iff C).mp ⟨pos,negs⟩
  obtain ⟨D,hmD,hD,heq,hmin⟩ := choose_minimumScore C hm good
  have hsize : D.size ≤ 63 := heq.le.trans hs
  by_cases hclean : ∀ a b : Fin 26, ¬edge (pairInput a b) → ¬∃ j, Owns 26 D j a b
  · obtain ⟨exactOutput, honest⟩ := clean_transfer D hmD hD hclean
    have bound : 64 ≤ D.size := cleanCost D hmD exactOutput honest
    omega
  · have found : ∃ j a b, Owns 26 D j a b ∧ ¬edge (pairInput a b) := by
      by_contra hn
      apply hclean
      intro a b hneg ⟨j, hj⟩
      exact hn ⟨j,a,b,hj,hneg⟩
    obtain ⟨j,a,b,owner,hneg⟩ := found
    have twoFlags := two_of_leaks D hmD hD hmin j owner.1 ⟨a,b,hneg,owner.2.2.1⟩
    have price : 64 ≤ D.size := dirtyCost D hmD hD (by
      refine ⟨j,a,b,owner,hneg,?_⟩
      obtain ⟨p,l,p2,l2,ne,h1,h2⟩ := twoFlags
      apply Finset.one_lt_card.mpr
      exact ⟨(p,l),Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
        (p2,l2),Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩,ne⟩)
    omega
