import Mathlib
import PEqualNP.Defs

-- Source: K-Yamada-2002, merged PR 2921, upstream commit 67b12c81a4864e00b7443c98602811c27825f5b7.

namespace PEqualNP.Outside.L_meta_1415_aux

-- The live-wire compression argument follows the project proof of L-meta-703.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search n ins = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht n ins nd (lift low run)
  exact Bool.noConfusion (rejection.symm.trans found)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search (m-2) ins = false)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩
end PEqualNP.Outside.L_meta_1415_aux

-- Per-word monotone upper netlists come from Seidler's five-input circuit catalog; their gates are checked below.

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
-- Kernel checks for the ten posted functions, using signed sampled words.

def ins_80000000 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000002aaaaaaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000004ccccccc, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000070f0f0f0, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000007f00ff00, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000007fff0000]

theorem nd_80000000 : ins_80000000.Nodup := by decide +kernel

theorem spec_80000000 : ∀ j : Fin 512, Nat.testBit 0x80000000 (∑ i : Fin 5, if (ins_80000000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_80000000 : search 2 ins_80000000 = false := by decide +kernel

def gates_80000000 : List Gate := [⟨.and, [4, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_80000000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0x80000000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_80000000, 8, ?_, rfl, ?_⟩
  · simp [gates_80000000]
  · decide +kernel

def ins_80808000 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000002a54aaa952a5554a952aaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000004c99333264c99993264ccc, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000070e1c3c3870e1e1c3870f0, 0xfffffffffffffffffffffffffffffffffffffffffffffffffc0000001fffffff0000000000000000000000000000000000000000007f01fc03f80fe01fc07f00, 0x7fffffffffffffe00000000000000000000000000000000000000000000000007ffe0003fff0001fff8000]

theorem nd_80808000 : ins_80808000.Nodup := by decide +kernel

theorem spec_80808000 : ∀ j : Fin 512, Nat.testBit 0x80808000 (∑ i : Fin 5, if (ins_80808000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_80808000 : search 2 ins_80808000 = false := by decide +kernel

def gates_80808000 : List Gate := [⟨.or, [4, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_80808000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0x80808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_80808000, 8, ?_, rfl, ?_⟩
  · simp [gates_80808000]
  · decide +kernel

def ins_88808000 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000004952aaa4952aaa4952aaa4952aaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000009264ccc9264ccc9264ccc9264ccc, 0xfffffffffffffffffffffffffffffffffffffffffff0000000ffffffffffffff000000000000000000000000000000000000e3870f0e3870f0e3870f0e3870f0, 0xffffffffffffffffffffffffffffffffffffffffffffffffff0000000fffffff000000000000000000000000000000000000fc07f00fc07f00fc07f00fc07f00, 0xfffffffffffffffffffff0000000000000000000000000000000000000000000fff8000fff8000fff8000fff8000]

theorem nd_88808000 : ins_88808000.Nodup := by decide +kernel

theorem spec_88808000 : ∀ j : Fin 512, Nat.testBit 0x88808000 (∑ i : Fin 5, if (ins_88808000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_88808000 : search 4 ins_88808000 = false := by decide +kernel

def gates_88808000 : List Gate := [⟨.or, [4, 3]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 9]⟩]

theorem upper_88808000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0x88808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_88808000, 10, ?_, rfl, ?_⟩
  · simp [gates_88808000]
  · decide +kernel

def ins_88808080 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000024a952a4952a5492a54a9254a9524a952a, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000493264c9264c9924c9932499326493264c, 0xfffffffffffffffffffffffffffffffffffff0000001ffffffffffffffffffff00000000000000000000000000000071c3870e3870e1c70e1c38e1c3871c3870, 0x7ffffffffffffe0000003ffffff80000000000000000000000000000000000007e03f80fc07f01f80fe03f01fc07e03f80, 0x7fffffffffffffffffffc00000000000000000000000000000000000000000007ffc000fff8001fff0003ffe0007ffc000]

theorem nd_88808080 : ins_88808080.Nodup := by decide +kernel

theorem spec_88808080 : ∀ j : Fin 512, Nat.testBit 0x88808080 (∑ i : Fin 5, if (ins_88808080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_88808080 : search 2 ins_88808080 = false := by decide +kernel

def gates_88808080 : List Gate := [⟨.and, [4, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_88808080 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0x88808080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_88808080, 8, ?_, rfl, ?_⟩
  · simp [gates_88808080]
  · decide +kernel

def ins_a8808080 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000012a54a84a952a12a54a84a952a12a54a84a952a, 0xfffffffffffffffffffffffffffffffc000000ffffffffffffffffffffffffff0000000000000000000000000a4c993293264ca4c993293264ca4c993293264c, 0xffffffffffffffffffffffffffffffffffffff0000003fffffffffffffffffff0000000000000000000000000c70e1c31c3870c70e1c31c3870c70e1c31c3870, 0xfffffffffffffffffffc000000ffffffc0000000000000000000000000000000f80fe03e03f80f80fe03e03f80f80fe03e03f80, 0xffffffffffffffffffffffffff00000000000000000000000000000000000000fff0003ffc000fff0003ffc000fff0003ffc000]

theorem nd_a8808080 : ins_a8808080.Nodup := by decide +kernel

theorem spec_a8808080 : ∀ j : Fin 512, Nat.testBit 0xa8808080 (∑ i : Fin 5, if (ins_a8808080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a8808080 : search 4 ins_a8808080 = false := by decide +kernel

def gates_a8808080 : List Gate := [⟨.or, [2, 1]⟩, ⟨.and, [2, 1]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [0, 9]⟩]

theorem upper_a8808080 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8808080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8808080, 10, ?_, rfl, ?_⟩
  · simp [gates_a8808080]
  · decide +kernel


def ins_88888880 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000024924a924925492492a49249524924a924925492492a, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000492493249249924924c924926492493249249924924c, 0xffffffffffffffffffffffffffc000001ffffff0000007fffffc000001ffffff0000000000000000000071c71c38e38e1c71c70e38e3871c71c38e38e1c71c70, 0x7fffffffffffe0000000000007fffffffffffe000000000000000000000000007e07e03f03f01f81f80fc0fc07e07e03f03f01f81f80, 0x7ffffffffffffffffffffffff8000000000000000000000000000000000000007ff8003ffc001ffe000fff0007ff8003ffc001ffe000]

theorem nd_88888880 : ins_88888880.Nodup := by decide +kernel

theorem spec_88888880 : ∀ j : Fin 512, Nat.testBit 0x88888880 (∑ i : Fin 5, if (ins_88888880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_88888880 : search 2 ins_88888880 = false := by decide +kernel

def gates_88888880 : List Gate := [⟨.or, [4, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_88888880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0x88888880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_88888880, 8, ?_, rfl, ?_⟩
  · simp [gates_88888880]
  · decide +kernel

def ins_a8808880 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000009524a84a925425492a12a49509524a84a925425492a, 0xffffffffffffffffffffffffffc000001fffffffffffffffffffffffffffffff00000000000000000000526493293249949924ca4c926526493293249949924c, 0xffffffffffffffffffffffffffffffffe000000ffffffffffffc000001ffffff0000000000000000000063871c31c38e18e1c70c70e3863871c31c38e18e1c70, 0x7ffffffffffffffffff0000007fffffffffffe000000000000000000000000007c07e03e03f01f01f80f80fc07c07e03e03f01f01f80, 0x7ffffffffffffffffffffffff8000000000000000000000000000000000000007ff8003ffc001ffe000fff0007ff8003ffc001ffe000]

theorem nd_a8808880 : ins_a8808880.Nodup := by decide +kernel

theorem spec_a8808880 : ∀ j : Fin 512, Nat.testBit 0xa8808880 (∑ i : Fin 5, if (ins_a8808880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a8808880 : search 4 ins_a8808880 = false := by decide +kernel

def gates_a8808880 : List Gate := [⟨.or, [3, 2]⟩, ⟨.and, [3, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [0, 9]⟩]

theorem upper_a8808880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8808880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8808880, 10, ?_, rfl, ?_⟩
  · simp [gates_a8808880]
  · decide +kernel

def ins_a888a000 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000922aa8491554248aaa1245550922aa8491554248aaa, 0x7fffffc000001ffffffffffffffffffffffffe00000000000000000000000000524b332925999492ccca49666524b332925999492ccc, 0xffffffffffffffffffffffffffffffffe000000ffffff8000003ffffffffffff00000000000000000000638c3c31c61e18e30f0c71878638c3c31c61e18e30f0, 0xfffffffffffffffffffffffffffffffffffffff0000000000003ffffffffffff000000000000000000007c0fc03e07e01f03f00f81f807c0fc03e07e01f03f00, 0x7ffffffffffffffffffffffffffffffc000000000000000000000000000000007ff0003ff8001ffc000ffe0007ff0003ff8001ffc000]

theorem nd_a888a000 : ins_a888a000.Nodup := by decide +kernel

theorem spec_a888a000 : ∀ j : Fin 512, Nat.testBit 0xa888a000 (∑ i : Fin 5, if (ins_a888a000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a888a000 : search 2 ins_a888a000 = false := by decide +kernel

def gates_a888a000 : List Gate := [⟨.and, [4, 1]⟩, ⟨.and, [3, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_a888a000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa888a000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a888a000, 8, ?_, rfl, ?_⟩
  · simp [gates_a888a000]
  · decide +kernel

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
-- Kernel checks for the ten posted functions, using signed sampled words.

def ins_a8808000 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000952aaa12a5554254aaa84a95550952aaa, 0xfffffffffffffffffffffffffffffffffffff0000001ffffffffffffffffffff0000000000000000000000000000005264ccca4c999949933329326665264ccc, 0xfffffffffffffffffffffffffffffffffffffffffffe0000003fffffffffffff00000000000000000000000000000063870f0c70e1e18e1c3c31c387863870f0, 0xffffffffffffffffffffffffffffffffffffffffffffffffffc0000007ffffff0000000000000000000000000000007c07f00f80fe01f01fc03e03f807c07f00, 0x7ffffffffffffffffffffffffff80000000000000000000000000000000000007ff8000fff0001ffe0003ffc0007ff8000]

theorem nd_a8808000 : ins_a8808000.Nodup := by decide +kernel

theorem spec_a8808000 : ∀ j : Fin 512, Nat.testBit 0xa8808000 (∑ i : Fin 5, if (ins_a8808000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a8808000 : search 6 ins_a8808000 = false := by decide +kernel

def gates_a8808000 : List Gate := [⟨.or, [4, 3]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [4, 3]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [0, 11]⟩]

theorem upper_a8808000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8808000, 12, ?_, rfl, ?_⟩
  · simp [gates_a8808000]
  · decide +kernel

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux

def gates_e8808000 : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [11, 13]⟩]

theorem upper_e8808000 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    ∧ gs.length = 10 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8808000, 14, ?_, rfl, ?_⟩
  · simp [gates_e8808000]
  · decide +kernel

def fourInputs : List W := [0xfffffffffffffffffffffffffffffffffffffffffffffffffffff001ffffffff0000000000000000000000000000000000000000000000000012a2544a89512a, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe003fffff0000000000000000000000000000000000000000000000000024c4989312624c, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc007ff000000000000000000000000000000000000000000000000004708e11c238470, 0x7ffffffffff80000000000000000000000000000000000000000000000000000780f01e03c0780]

theorem four_distinct : fourInputs.Nodup := by decide +kernel

theorem four_row : ∀ j : Fin 512, Nat.testBit 0xe880
    (∑ i : Fin 4, if (fourInputs.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by
  decide +kernel

set_option maxRecDepth 32000
set_option maxHeartbeats 80000000
def rr0 : W := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffff001ffffffff0000000000000000000000000000000000000000000000000012a2544a89512a
def rr1 : W := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe003fffff0000000000000000000000000000000000000000000000000024c4989312624c
def rr2 : W := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc007ff000000000000000000000000000000000000000000000000004708e11c238470
def rr3 : W := 0x7ffffffffff80000000000000000000000000000000000000000000000000000780f01e03c0780

def rBranch (a b : W) (r : List W) (w : W) : Bool :=
  let v := sep w ||| cuts r
  ((v == -1) && optimized 5 3 (w :: r)) ||
    ((3 != (0 : ℕ)) && (((v ||| sep a == -1) && optimized 5 2 (w :: a :: r)) ||
                        ((v ||| sep b == -1) && optimized 5 2 (w :: b :: r)))) ||
    ((3 ≥ (2 : ℕ)) && (v ||| sep a ||| sep b == -1) && optimized 5 1 (w :: a :: b :: r))


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r01op0 : rBranch rr0 rr1 [rr2, rr3] (rr0 &&& rr1) = false := by decide +kernel
private theorem r01op1 : rBranch rr0 rr1 [rr2, rr3] (rr0 ||| rr1) = false := by decide +kernel
private theorem r01op2 : rBranch rr0 rr1 [rr2, rr3] (rr0 &&& ~~~rr1) = false := by decide +kernel
private theorem r01op3 : rBranch rr0 rr1 [rr2, rr3] (rr1 &&& ~~~rr0) = false := by decide +kernel
theorem r01pair : dispatch 3 (optimized 5) rr0 rr1 [rr2, rr3] = false := by
  change (ops rr0 rr1).any (rBranch rr0 rr1 [rr2, rr3]) = false
  simp only [ops, List.any_cons, List.any_nil, r01op0, r01op1, r01op2, r01op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r02op0 : rBranch rr0 rr2 [rr1, rr3] (rr0 &&& rr2) = false := by decide +kernel
private theorem r02op1 : rBranch rr0 rr2 [rr1, rr3] (rr0 ||| rr2) = false := by decide +kernel
private theorem r02op2 : rBranch rr0 rr2 [rr1, rr3] (rr0 &&& ~~~rr2) = false := by decide +kernel
private theorem r02op3 : rBranch rr0 rr2 [rr1, rr3] (rr2 &&& ~~~rr0) = false := by decide +kernel
theorem r02pair : dispatch 3 (optimized 5) rr0 rr2 [rr1, rr3] = false := by
  change (ops rr0 rr2).any (rBranch rr0 rr2 [rr1, rr3]) = false
  simp only [ops, List.any_cons, List.any_nil, r02op0, r02op1, r02op2, r02op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r03op0 : rBranch rr0 rr3 [rr1, rr2] (rr0 &&& rr3) = false := by decide +kernel
private theorem r03op1 : rBranch rr0 rr3 [rr1, rr2] (rr0 ||| rr3) = false := by decide +kernel
private theorem r03op2 : rBranch rr0 rr3 [rr1, rr2] (rr0 &&& ~~~rr3) = false := by decide +kernel
private theorem r03op3 : rBranch rr0 rr3 [rr1, rr2] (rr3 &&& ~~~rr0) = false := by decide +kernel
theorem r03pair : dispatch 3 (optimized 5) rr0 rr3 [rr1, rr2] = false := by
  change (ops rr0 rr3).any (rBranch rr0 rr3 [rr1, rr2]) = false
  simp only [ops, List.any_cons, List.any_nil, r03op0, r03op1, r03op2, r03op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r12op0 : rBranch rr1 rr2 [rr0, rr3] (rr1 &&& rr2) = false := by decide +kernel
private theorem r12op1 : rBranch rr1 rr2 [rr0, rr3] (rr1 ||| rr2) = false := by decide +kernel
private theorem r12op2 : rBranch rr1 rr2 [rr0, rr3] (rr1 &&& ~~~rr2) = false := by decide +kernel
private theorem r12op3 : rBranch rr1 rr2 [rr0, rr3] (rr2 &&& ~~~rr1) = false := by decide +kernel
theorem r12pair : dispatch 3 (optimized 5) rr1 rr2 [rr0, rr3] = false := by
  change (ops rr1 rr2).any (rBranch rr1 rr2 [rr0, rr3]) = false
  simp only [ops, List.any_cons, List.any_nil, r12op0, r12op1, r12op2, r12op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r13op0 : rBranch rr1 rr3 [rr0, rr2] (rr1 &&& rr3) = false := by decide +kernel
private theorem r13op1 : rBranch rr1 rr3 [rr0, rr2] (rr1 ||| rr3) = false := by decide +kernel
private theorem r13op2 : rBranch rr1 rr3 [rr0, rr2] (rr1 &&& ~~~rr3) = false := by decide +kernel
private theorem r13op3 : rBranch rr1 rr3 [rr0, rr2] (rr3 &&& ~~~rr1) = false := by decide +kernel
theorem r13pair : dispatch 3 (optimized 5) rr1 rr3 [rr0, rr2] = false := by
  change (ops rr1 rr3).any (rBranch rr1 rr3 [rr0, rr2]) = false
  simp only [ops, List.any_cons, List.any_nil, r13op0, r13op1, r13op2, r13op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem r23op0 : rBranch rr2 rr3 [rr0, rr1] (rr2 &&& rr3) = false := by decide +kernel
private theorem r23op1 : rBranch rr2 rr3 [rr0, rr1] (rr2 ||| rr3) = false := by decide +kernel
private theorem r23op2 : rBranch rr2 rr3 [rr0, rr1] (rr2 &&& ~~~rr3) = false := by decide +kernel
private theorem r23op3 : rBranch rr2 rr3 [rr0, rr1] (rr3 &&& ~~~rr2) = false := by decide +kernel
theorem r23pair : dispatch 3 (optimized 5) rr2 rr3 [rr0, rr1] = false := by
  change (ops rr2 rr3).any (rBranch rr2 rr3 [rr0, rr1]) = false
  simp only [ops, List.any_cons, List.any_nil, r23op0, r23op1, r23op2, r23op3, Bool.false_or]


end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux
set_option maxRecDepth 32000
set_option maxHeartbeats 80000000

private theorem fourFullReject : optimized 6 3 fourInputs = false := by
  have eqs : pairs fourInputs = [(rr0, rr1, [rr2, rr3]), (rr0, rr2, [rr1, rr3]), (rr0, rr3, [rr1, rr2]), (rr1, rr2, [rr0, rr3]), (rr1, rr3, [rr0, rr2]), (rr2, rr3, [rr0, rr1])] := rfl
  have hgoal : (fourInputs == [goal] || fourInputs == [~~~goal]) = false := by decide +kernel
  rewrite [optimized, hgoal, Bool.false_or, eqs]
  simp only [List.any_cons, List.any_nil, r01pair, r02pair, r03pair, r12pair, r13pair, r23pair, Bool.false_or]

private theorem four_all : fourInputs.sublists.filter
    (fun ws => decide (ws.length ≤ 6+1) && (cuts ws == -1)) = [fourInputs] := by
  decide +kernel

theorem four_reject : search 6 fourInputs = false := by
  unfold search
  rewrite [← List.any_filter, four_all]
  change (optimized 6 3 fourInputs || false) = false
  simp only [fourFullReject, Bool.false_or]

theorem four_lower (g : W) (hg : g=goal ∨ g= ~~~goal) :
    ¬ build basicOps g 6 fourInputs.toFinset := by
  intro h
  have yes := search_complete hg 6 fourInputs four_distinct h
  rw [four_reject] at yes
  contradiction

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux

set_option maxRecDepth 32000
set_option maxHeartbeats 8000000

def fullInputs : List W := [0xfffffffffffffffffffffffffffffffc000000ffffffffffffffffffffffffff0000000000000000000000000254aaa8952aaa254aaa8952aaa254aaa8952aaa, 0xffffffffffffffffffffffffffffffffffffff0000003fffffffffffffffffff00000000000000000000000004993331264ccc4993331264ccc4993331264ccc, 0xffffffffffffffffffffffffffffffffffffffffffffc000000fffffffffffff00000000000000000000000008e1c3c23870f08e1c3c23870f08e1c3c23870f0, 0xfffffffffffffffffffffffffffffffffffffffffffffffffff0000003ffffff0000000000000000000000000f01fc03c07f00f01fc03c07f00f01fc03c07f00, 0xffffffffffffffffffffffffffffffffc0000000000000000000000000000000ffe0003ff8000ffe0003ff8000ffe0003ff8000]

theorem full_width : fullInputs.length = 5 := rfl
theorem full_nd : fullInputs.Nodup := by decide +kernel
theorem full_rows : ∀ j : Fin 512, Nat.testBit 0xe8808000
    (∑ i : Fin 5, if (fullInputs.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by
  decide +kernel


def dataAt (i : Fin 5) : W := fullInputs.getD i.val 0

def dataOp (a b : W) (d : Fin 4) : W := (ops a b).getD d.val 0

def anchorTable : Array Nat := #[0, 0, 0, 0, 103, 14, 14, 103, 76, 14, 14, 76, 47, 14, 14, 47, 14, 47, 47, 14, 129, 13, 13, 129, 0, 0, 0, 0, 75, 13, 13, 75, 46, 13, 13, 46, 13, 46, 46, 13, 128, 11, 11, 128, 101, 11, 11, 101, 0, 0, 0, 0, 44, 11, 11, 44, 11, 44, 44, 11, 125, 7, 7, 125, 98, 7, 7, 98, 70, 7, 7, 70, 0, 0, 0, 0, 7, 70, 70, 7, 118, 33, 33, 118, 91, 33, 33, 91, 63, 33, 33, 63, 33, 63, 63, 33, 0, 0, 0, 0]

def anchor (i j : Fin 5) (d : Fin 4) : Fin 256 :=
  Fin.ofNat 256 (anchorTable.getD ((i.val * 5 + j.val) * 4 + d.val) 0)

theorem data_index {w : W} (h : w ∈ fullInputs) : ∃ i : Fin 5, dataAt i = w := by
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨i,by simpa only [full_width] using hi⟩,?_⟩
  simpa only [dataAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using e

theorem op_index {a b z : W} (h : z ∈ ops a b) : ∃ d : Fin 4, dataOp a b d = z := by
  obtain ⟨d,hd,e⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨d,by simpa only [ops,List.length_cons,List.length_nil] using hd⟩,?_⟩
  simpa only [dataOp,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hd,Option.getD_some] using e

def anchorOK (i j : Fin 5) (d : Fin 4) : Prop :=
  let k := anchor i j d
  differs k (dataAt i) ∧ ¬differs k (dataOp (dataAt i) (dataAt j) d) ∧
    ∀ v : Fin 5, v ≠ i → ¬differs k (dataAt v)

private theorem anchor_0 : ∀ j : Fin 5, ∀ d : Fin 4, (0 : Fin 5) ≠ j → anchorOK 0 j d := by
  unfold anchorOK differs
  decide +kernel

private theorem anchor_1 : ∀ j : Fin 5, ∀ d : Fin 4, (1 : Fin 5) ≠ j → anchorOK 1 j d := by
  unfold anchorOK differs
  decide +kernel

private theorem anchor_2 : ∀ j : Fin 5, ∀ d : Fin 4, (2 : Fin 5) ≠ j → anchorOK 2 j d := by
  unfold anchorOK differs
  decide +kernel

private theorem anchor_3 : ∀ j : Fin 5, ∀ d : Fin 4, (3 : Fin 5) ≠ j → anchorOK 3 j d := by
  unfold anchorOK differs
  decide +kernel

private theorem anchor_4 : ∀ j : Fin 5, ∀ d : Fin 4, (4 : Fin 5) ≠ j → anchorOK 4 j d := by
  unfold anchorOK differs
  decide +kernel

theorem pivot_rows : ∀ a ∈ fullInputs, ∀ b ∈ fullInputs, a ≠ b → ∀ z ∈ ops a b,
    ∃ i : Fin 256, differs i a ∧ ¬ differs i z ∧ ∀ w ∈ fullInputs, w ≠ a → ¬ differs i w := by
  intro a ha b hb hne z hz
  obtain ⟨i,rfl⟩ := data_index ha
  obtain ⟨j,rfl⟩ := data_index hb
  obtain ⟨d,rfl⟩ := op_index hz
  have ij : i ≠ j := fun e => hne (congrArg dataAt e)
  have checked : anchorOK i j d := by
    fin_cases i
    · exact anchor_0 j d ij
    · exact anchor_1 j d ij
    · exact anchor_2 j d ij
    · exact anchor_3 j d ij
    · exact anchor_4 j d ij
  obtain ⟨h1,h2,h3⟩ := checked
  refine ⟨anchor i j d,h1,h2,?_⟩
  intro w hw neq
  obtain ⟨v,rfl⟩ := data_index hw
  exact h3 v (fun e => neq (congrArg dataAt e))

def sampledFour : List W := [0xfffffffffffffffffffffffffffffffffffffffffffffffffffff001ffffffff0000000000000000000000000000000000000000000000000012a2544a89512a, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe003fffff0000000000000000000000000000000000000000000000000024c4989312624c, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc007ff000000000000000000000000000000000000000000000000004708e11c238470, 0x7ffffffffff80000000000000000000000000000000000000000000000000000780f01e03c0780]

private def coordinates : Array (Array Nat) := #[#[1, 3, 5, 7, 9, 11, 13, 16, 18, 20, 23, 27, 29, 31, 33, 35, 37, 39, 42, 44, 46, 49, 53, 55, 57, 59, 61, 63, 65, 68, 70, 72, 75, 79, 81, 83, 85, 87, 89, 91, 94, 96, 98, 101, 131, 133, 135, 137, 139, 141, 143, 146, 148, 150, 153], #[2, 3, 6, 7, 10, 11, 14, 17, 18, 21, 24, 28, 29, 32, 33, 36, 37, 40, 43, 44, 47, 50, 54, 55, 58, 59, 62, 63, 66, 69, 70, 73, 76, 106, 107, 110, 111, 114, 115, 118, 121, 122, 125, 128, 132, 133, 136, 137, 140, 141, 144, 147, 148, 151, 154], #[4, 5, 6, 7, 12, 13, 14, 19, 20, 21, 25, 30, 31, 32, 33, 38, 39, 40, 45, 46, 47, 51, 82, 83, 84, 85, 90, 91, 92, 97, 98, 99, 103, 108, 109, 110, 111, 116, 117, 118, 123, 124, 125, 129, 134, 135, 136, 137, 142, 143, 144, 149, 150, 151, 155], #[8, 9, 10, 11, 12, 13, 14, 22, 23, 24, 25, 60, 61, 62, 63, 64, 65, 66, 74, 75, 76, 77, 86, 87, 88, 89, 90, 91, 92, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 126, 127, 128, 129, 138, 139, 140, 141, 142, 143, 144, 152, 153, 154, 155], #[41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]]

def coord (i : Fin 5) (k : Fin 512) : Fin 512 :=
  let a := k.val % 256
  let j := (coordinates[i.val]!).getD (if a < 55 then a else 0) 0
  Fin.ofNat 512 (j + (if k.val < 256 then 0 else 256))

theorem coord_goal : ∀ (i : Fin 5) (k : Fin 512),
    goal[(coord i k).val] = goal[k.val] := by decide +kernel

theorem coord_true : ∀ (i : Fin 5) (k : Fin 512),
    (fullInputs.getD i.val 0)[(coord i k).val] = true := by decide +kernel

private theorem c00 : ∀ k : Fin 512, (fullInputs.getD ((0 : Fin 5).succAbove (0 : Fin 4)).val 0)[(coord 0 k).val] = (sampledFour.getD 0 0)[k.val] := by decide +kernel

private theorem c01 : ∀ k : Fin 512, (fullInputs.getD ((0 : Fin 5).succAbove (1 : Fin 4)).val 0)[(coord 0 k).val] = (sampledFour.getD 1 0)[k.val] := by decide +kernel

private theorem c02 : ∀ k : Fin 512, (fullInputs.getD ((0 : Fin 5).succAbove (2 : Fin 4)).val 0)[(coord 0 k).val] = (sampledFour.getD 2 0)[k.val] := by decide +kernel

private theorem c03 : ∀ k : Fin 512, (fullInputs.getD ((0 : Fin 5).succAbove (3 : Fin 4)).val 0)[(coord 0 k).val] = (sampledFour.getD 3 0)[k.val] := by decide +kernel

private theorem c10 : ∀ k : Fin 512, (fullInputs.getD ((1 : Fin 5).succAbove (0 : Fin 4)).val 0)[(coord 1 k).val] = (sampledFour.getD 0 0)[k.val] := by decide +kernel

private theorem c11 : ∀ k : Fin 512, (fullInputs.getD ((1 : Fin 5).succAbove (1 : Fin 4)).val 0)[(coord 1 k).val] = (sampledFour.getD 1 0)[k.val] := by decide +kernel

private theorem c12 : ∀ k : Fin 512, (fullInputs.getD ((1 : Fin 5).succAbove (2 : Fin 4)).val 0)[(coord 1 k).val] = (sampledFour.getD 2 0)[k.val] := by decide +kernel

private theorem c13 : ∀ k : Fin 512, (fullInputs.getD ((1 : Fin 5).succAbove (3 : Fin 4)).val 0)[(coord 1 k).val] = (sampledFour.getD 3 0)[k.val] := by decide +kernel

private theorem c20 : ∀ k : Fin 512, (fullInputs.getD ((2 : Fin 5).succAbove (0 : Fin 4)).val 0)[(coord 2 k).val] = (sampledFour.getD 0 0)[k.val] := by decide +kernel

private theorem c21 : ∀ k : Fin 512, (fullInputs.getD ((2 : Fin 5).succAbove (1 : Fin 4)).val 0)[(coord 2 k).val] = (sampledFour.getD 1 0)[k.val] := by decide +kernel

private theorem c22 : ∀ k : Fin 512, (fullInputs.getD ((2 : Fin 5).succAbove (2 : Fin 4)).val 0)[(coord 2 k).val] = (sampledFour.getD 2 0)[k.val] := by decide +kernel

private theorem c23 : ∀ k : Fin 512, (fullInputs.getD ((2 : Fin 5).succAbove (3 : Fin 4)).val 0)[(coord 2 k).val] = (sampledFour.getD 3 0)[k.val] := by decide +kernel

private theorem c30 : ∀ k : Fin 512, (fullInputs.getD ((3 : Fin 5).succAbove (0 : Fin 4)).val 0)[(coord 3 k).val] = (sampledFour.getD 0 0)[k.val] := by decide +kernel

private theorem c31 : ∀ k : Fin 512, (fullInputs.getD ((3 : Fin 5).succAbove (1 : Fin 4)).val 0)[(coord 3 k).val] = (sampledFour.getD 1 0)[k.val] := by decide +kernel

private theorem c32 : ∀ k : Fin 512, (fullInputs.getD ((3 : Fin 5).succAbove (2 : Fin 4)).val 0)[(coord 3 k).val] = (sampledFour.getD 2 0)[k.val] := by decide +kernel

private theorem c33 : ∀ k : Fin 512, (fullInputs.getD ((3 : Fin 5).succAbove (3 : Fin 4)).val 0)[(coord 3 k).val] = (sampledFour.getD 3 0)[k.val] := by decide +kernel

private theorem c40 : ∀ k : Fin 512, (fullInputs.getD ((4 : Fin 5).succAbove (0 : Fin 4)).val 0)[(coord 4 k).val] = (sampledFour.getD 0 0)[k.val] := by decide +kernel

private theorem c41 : ∀ k : Fin 512, (fullInputs.getD ((4 : Fin 5).succAbove (1 : Fin 4)).val 0)[(coord 4 k).val] = (sampledFour.getD 1 0)[k.val] := by decide +kernel

private theorem c42 : ∀ k : Fin 512, (fullInputs.getD ((4 : Fin 5).succAbove (2 : Fin 4)).val 0)[(coord 4 k).val] = (sampledFour.getD 2 0)[k.val] := by decide +kernel

private theorem c43 : ∀ k : Fin 512, (fullInputs.getD ((4 : Fin 5).succAbove (3 : Fin 4)).val 0)[(coord 4 k).val] = (sampledFour.getD 3 0)[k.val] := by decide +kernel

theorem coord_other : ∀ (i : Fin 5) (a : Fin 4) (k : Fin 512),
    (fullInputs.getD (i.succAbove a).val 0)[(coord i k).val] = (sampledFour.getD a.val 0)[k.val] := by
  intro i a
  fin_cases i <;> fin_cases a
  · exact c00
  · exact c01
  · exact c02
  · exact c03
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c30
  · exact c31
  · exact c32
  · exact c33
  · exact c40
  · exact c41
  · exact c42
  · exact c43

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux

def flat (w : W) := w = 0 ∨ w = ~~~0

set_option maxRecDepth 5000 in
theorem flat_free (av : Finset W) (a b z : W) (ha : holds av a) (hb : holds av b)
    (hf : flat a ∨ flat b) (hz : z ∈ basicOps a b) : holds av z := by
  have zero : holds av (0 : W) := .inl rfl
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have ac (x y : W) (fx : flat x) (hy : holds av y) : holds av (x &&& y) := by
    rcases fx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact zero
    · change holds av (BitVec.allOnes 512 &&& y)
      rw [BitVec.allOnes_and]; exact hy
  have oc (x y : W) (fx : flat x) (hy : holds av y) : holds av (x ||| y) := by
    rcases fx with rfl|rfl
    · rw [show (0 : W) ||| y = y from BitVec.zero_or]; exact hy
    · change holds av (BitVec.allOnes 512 ||| y)
      rw [BitVec.allOnes_or]
      exact .inr (.inl rfl)
  have fnc (x : W) (fx : flat x) : flat (~~~x) := by
    rcases fx with rfl|rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  rcases hf with fa|fb
  · rcases hz with rfl|rfl|rfl|rfl
    · exact ac _ _ fa hb
    · exact oc _ _ fa hb
    · exact ac _ _ fa (holds_not hb)
    · rw [BitVec.and_comm]; exact ac _ _ (fnc _ fa) hb
  · rcases hz with rfl|rfl|rfl|rfl
    · rw [BitVec.and_comm]; exact ac _ _ fb ha
    · rw [BitVec.or_comm]; exact oc _ _ fb ha
    · rw [BitVec.and_comm]; exact ac _ _ (fnc _ fb) ha
    · exact ac _ _ fb (holds_not ha)

theorem any_reach (av : Finset W) (a b z : W) (ha : holds av a) (hb : holds av b)
    (hz : z ∈ basicOps a b) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)

theorem build_up {av : Finset W} {g : W} {k m : ℕ} (h : k ≤ m)
    (hr : build basicOps g k av) : build basicOps g m av := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Or.inl ih

theorem project_live (P : W → W)
    (pres : ∀ a b z, z ∈ basicOps a b → P z ∈ basicOps (P a) (P b))
    {t : W} (ht : ¬ flat (P t)) (k : ℕ) (s : Finset W) (run : live basicOps t k s)
    (av : Finset W) (supply : ∀ v ∈ s, holds av (P v)) (m : ℕ)
    (room : k ≤ m ∨ (k ≤ m+1 ∧ ∃ v ∈ s, flat (P v))) :
    ∃ g, (P t = g ∨ P t = ~~~g) ∧ build basicOps g m av := by
  induction k generalizing s av m with
  | zero =>
    change s = {t} at run
    have h := supply t (by simp [run])
    rcases h with h|h|⟨g,hg,eq⟩
    · exact False.elim (ht (.inl h))
    · exact False.elim (ht (.inr h))
    · exact ⟨g,eq,build_up (Nat.zero_le m) (show build basicOps g 0 av from hg)⟩
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,_,rest,hs,next⟩
    · apply ih s skip av supply m
      rcases room with h|⟨h,other⟩
      · exact .inl (by omega)
      · exact .inr ⟨by omega,other⟩
    have incl : rest ⊆ s := by
      intro v hv
      rw [hs]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)
    have az := pres a b z hz
    by_cases free : holds av (P z)
    · apply ih (insert z rest) next av _ m (.inl (by rcases room with h|⟨h,_⟩ <;> omega))
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · exact free
      · exact supply _ (incl hr)
    · obtain ⟨x,hx,y,hy,hxy,u,hu,pu⟩ := (any_reach av _ _ _ (supply a ha) (supply b hb) az).resolve_left free
      have noflat : ¬(flat (P a) ∨ flat (P b)) :=
        fun h => free (flat_free _ _ _ _ (supply _ ha) (supply _ hb) h az)
      have pass : (∃ w ∈ s, flat (P w)) → ∃ w ∈ insert z rest, flat (P w) := by
        rintro ⟨w,hw,fw⟩
        rw [hs] at hw
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact False.elim (noflat (.inl fw))
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact False.elim (noflat (.inr fw))
        · exact ⟨w,Finset.mem_insert_of_mem hw,fw⟩
      cases m with
      | zero =>
        rcases room with h|⟨h,f⟩
        · omega
        have hk : k=0 := by omega
        subst k
        change insert z rest = {t} at next
        obtain ⟨w,hw,fw⟩ := pass f
        rw [next, Finset.mem_singleton] at hw
        exact False.elim (ht (hw ▸ fw))
      | succ m =>
        obtain ⟨g,eq,tail⟩ := ih _ next (insert u av) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl|hr
          · exact pu
          · exact holds_insert (supply _ (incl hr))) m (by
            rcases room with h|⟨h,f⟩
            · exact .inl (by omega)
            · exact .inr ⟨by omega,pass f⟩)
        exact ⟨g,eq,Or.inr ⟨x,hx,y,hy,hxy,u,hu,tail⟩⟩

def pick (σ : Fin 512 → Fin 512) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k : Fin 512 => w[(σ k).val])).cast List.length_ofFn

theorem pick_at (σ : Fin 512 → Fin 512) (w : W) (j : ℕ) (hj : j < 512) :
    (pick σ w)[j] = w[(σ ⟨j,hj⟩).val] := by
  change (pick σ w).getLsbD j = _
  simp only [pick, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem pick_not (σ : Fin 512 → Fin 512) (w : W) : pick σ (~~~w) = ~~~pick σ w :=
  BitVec.eq_of_getElem_eq fun j hj => by simp [pick_at]

theorem pick_basic (σ : Fin 512 → Fin 512) (a b z : W) (hz : z ∈ basicOps a b) :
    pick σ z ∈ basicOps (pick σ a) (pick σ b) := by
  have hAnd (x y : W) : pick σ (x &&& y) = pick σ x &&& pick σ y :=
    BitVec.eq_of_getElem_eq fun j hj => by simp [pick_at]
  have hOr (x y : W) : pick σ (x ||| y) = pick σ x ||| pick σ y :=
    BitVec.eq_of_getElem_eq fun j hj => by simp [pick_at]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl <;> simp [hAnd,hOr,pick_not]

theorem first_retained {inp needed : Finset W} {t a z : W} {k : ℕ}
    (ht : t = goal ∨ t = ~~~goal) (cut : ∃ i, ¬ differs i z ∧ ∀ w ∈ inp, w ≠ a → ¬ differs i w)
    (hn : needed ⊆ inp) (tail : live basicOps t k (insert z needed)) : a ∈ needed := by
  by_contra bad
  obtain ⟨i,hz,ho⟩ := cut
  have allDt : ∀ j, differs j t := by
    rcases ht with rfl|rfl <;> unfold differs <;> decide +kernel
  have dt := allDt i
  obtain ⟨w,hw,d⟩ := live_separates (differs i) dt (ops_differs i) tail
  rcases Finset.mem_insert.mp hw with rfl|h
  · exact hz d
  · exact ho w (hn h) (fun e => bad (e ▸ h)) d

theorem after_first {a b z t : W} {rest av : Finset W} (F : W → W)
    (hom : ∀ a b z, z ∈ basicOps a b → F z ∈ basicOps (F a) (F b))
    (ht : ¬ flat (F t)) (ha : a ∈ rest) (hf : flat (F a))
    (hb : holds av (F b)) (hz : z ∈ basicOps a b)
    (hr : ∀ v ∈ rest, holds av (F v))
    (tail : live basicOps t 7 (insert z rest)) :
    ∃ g, (F t = g ∨ F t = ~~~g) ∧ build basicOps g 6 av := by
  apply project_live F hom ht 7 _ tail av _ 6 (.inr ⟨by decide,a,Finset.mem_insert_of_mem ha,hf⟩)
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl|hm
  · exact flat_free av _ _ _ (hr a ha) hb (.inl hf) (hom _ _ _ hz)
  · exact hr _ hm

theorem obstruct_eight (inp four : List W)
    (absent : goal ∉ inp ∧ ~~~goal ∉ inp)
    (distinguish : ∀ a ∈ inp, ∀ b ∈ inp, a ≠ b → ∀ z ∈ basicOps a b,
      ∃ i, ¬ differs i z ∧ ∀ w ∈ inp.toFinset, w ≠ a → ¬ differs i w)
    (projections : ∀ a ∈ inp, ∃ σ : Fin 512 → Fin 512,
      flat (pick σ a) ∧ pick σ goal = goal ∧ ∀ w ∈ inp, holds four.toFinset (pick σ w))
    (lower : ∀ g, (g = goal ∨ g = ~~~goal) → ¬build basicOps g 6 four.toFinset)
    (t : W) (target : t = goal ∨ t = ~~~goal) : ¬build basicOps t 8 inp.toFinset := by
  intro run
  obtain ⟨s,hs,ls⟩ := compress run
  rcases first_live (k:=7) ls with done|⟨a,ha,b,hb,ne,z,hz,_,rest,heq,tail⟩
  · have inside : t ∈ inp := List.mem_toFinset.mp (hs (by simp [done]))
    rcases target with rfl|rfl
    · exact absent.1 inside
    · exact absent.2 inside
  · have ai := List.mem_toFinset.mp (hs ha)
    have bi := List.mem_toFinset.mp (hs hb)
    have restsub : rest ⊆ inp.toFinset := by
      intro v hv
      apply hs
      rw [heq]
      simp [hv]
    have retained := first_retained target (distinguish a ai b bi ne z hz) restsub tail
    obtain ⟨σ,hflat,hgoal,available⟩ := projections a ai
    have residual : pick σ t = goal ∨ pick σ t = ~~~goal := by
      rcases target with rfl|rfl
      · exact .inl hgoal
      · exact .inr (by rw [pick_not,hgoal])
    have nonflat : ¬ flat (pick σ t) := by
      rcases residual with h|h <;> rw [h] <;> unfold flat <;> decide +kernel
    obtain ⟨g,sign,pr⟩ := after_first (pick σ) (pick_basic σ) nonflat retained hflat
      (available b bi) hz (fun v hv => available v (List.mem_toFinset.mp (restsub hv))) tail
    apply lower g _ pr
    rcases sign with e|e <;> rcases residual with u|u
    · exact .inl (e.symm.trans u)
    · exact .inr (e.symm.trans u)
    · exact .inr (by rw [← u, e, BitVec.not_not])
    · exact .inl (by simpa only [BitVec.not_not] using congrArg (fun x : W => ~~~x) (e.symm.trans u))

open PEqualNP.CircuitLowerBounds

theorem native_build (T : ℕ) (inp : List W) (width : inp.length = 5)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (inp.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) inp.toFinset := by
  apply compile gs o hg inp inp.toFinset (fun u hu => .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩))
  intro k
  change Circuit.eval ⟨gs,o⟩ (inp.map fun w : W => w[k.val]) = goal[k.val]
  let x (i : Fin 5) : Bool := (inp.getD i.val 0)[k.val]
  have same : List.ofFn x = inp.map fun w : W => w[k.val] := by
    apply List.ext_getElem
    · simp [width]
    · intro i hi hj
      have hlt : i < inp.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [← same, he]
  exact row k

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1415_aux
namespace PEqualNP.Outside.L_meta_1415_aux

private theorem ones_bit (k : Fin 512) : (~~~(0 : W)).getLsbD k.val = true := by
  rw [BitVec.getLsbD_not]
  simp [k.isLt]

theorem input_index (w : W) (hm : w ∈ fullInputs) : ∃ i : Fin 5, fullInputs.getD i.val 0 = w := by
  obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hm
  refine ⟨⟨j,by simpa [full_width] using hj⟩,?_⟩
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using e

theorem restrictions (a : W) (ha : a ∈ fullInputs) : ∃ σ : Fin 512 → Fin 512,
    flat (pick σ a) ∧ pick σ goal = goal ∧ ∀ w ∈ fullInputs, holds fourInputs.toFinset (pick σ w) := by
  obtain ⟨i,ei⟩ := input_index a ha
  have one : pick (coord i) a = ~~~0 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [pick_at,← ei,coord_true i ⟨j,hj⟩]
    exact (ones_bit ⟨j,hj⟩).symm
  refine ⟨coord i,Or.inr one,?_,?_⟩
  · exact BitVec.eq_of_getElem_eq fun j hj => (pick_at _ _ _ _).trans (coord_goal i ⟨j,hj⟩)
  · intro w hw
    obtain ⟨l,el⟩ := input_index w hw
    by_cases eq : l = i
    · subst l
      rw [← el,ei,one]
      exact .inr (.inl rfl)
    · obtain ⟨v,ev⟩ := Fin.exists_succAbove_eq eq
      have hh : pick (coord i) w = fourInputs.getD v.val 0 := by
        apply BitVec.eq_of_getElem_eq
        intro j hj
        rw [pick_at,← el,← ev]
        exact coord_other i v ⟨j,hj⟩
      have hl : v.val < fourInputs.length := by change v.val < 4; exact v.isLt
      refine .inr (.inr ⟨fourInputs.getD v.val 0,List.mem_toFinset.mpr ?_,Or.inl hh⟩)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_mem hl

theorem no_eight (t : W) (ht : t = goal ∨ t = ~~~goal) : ¬build basicOps t 8 fullInputs.toFinset := by
  apply obstruct_eight fullInputs fourInputs (by decide +kernel) _ restrictions four_lower t ht
  intro a ha b hb hne z hz
  obtain ⟨i,_,hx,hw⟩ := pivot_rows a ha b hb hne z (List.mem_toFinset.mp hz)
  exact ⟨i,hx,fun v hv => hw v (List.mem_toFinset.mp hv)⟩

theorem exception_lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit 0xe8808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    9 ≤ binaryCost gs := by
  obtain ⟨t,ht,run⟩ := native_build _ _ full_width full_rows gs o hg he
  by_contra! low
  exact no_eight t ht (build_up (by omega) run)

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1415_aux

theorem replace_threshold (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit 0xe8808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit 0xe8808000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
      ⟨g,hm,by simp [isBinary, hn]⟩
    have low := exception_lower gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper_e8808000
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

end PEqualNP.Outside.L_meta_1415_aux
open PEqualNP.Outside.L_meta_1415_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1415 : ∀ T ∈ ({0x80000000, 0x80808000, 0x88808000, 0x88808080, 0xa8808000, 0xa8808080, 0xe8808000, 0x88888880, 0xa8808880, 0xa888a000} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0x80000000 4 ins_80000000 nd_80000000 spec_80000000 rfl reject_80000000 upper_80000000 gs o hg he
  · exact replace 0x80808000 4 ins_80808000 nd_80808000 spec_80808000 rfl reject_80808000 upper_80808000 gs o hg he
  · exact replace 0x88808000 6 ins_88808000 nd_88808000 spec_88808000 rfl reject_88808000 upper_88808000 gs o hg he
  · exact replace 0x88808080 4 ins_88808080 nd_88808080 spec_88808080 rfl reject_88808080 upper_88808080 gs o hg he
  · exact replace 0xa8808000 8 ins_a8808000 nd_a8808000 spec_a8808000 rfl reject_a8808000 upper_a8808000 gs o hg he
  · exact replace 0xa8808080 6 ins_a8808080 nd_a8808080 spec_a8808080 rfl reject_a8808080 upper_a8808080 gs o hg he
  · exact replace_threshold gs o hg he
  · exact replace 0x88888880 4 ins_88888880 nd_88888880 spec_88888880 rfl reject_88888880 upper_88888880 gs o hg he
  · exact replace 0xa8808880 6 ins_a8808880 nd_a8808880 spec_a8808880 rfl reject_a8808880 upper_a8808880 gs o hg he
  · exact replace 0xa888a000 4 ins_a888a000 nd_a888a000 spec_a888a000 rfl reject_a888a000 upper_a888a000 gs o hg he
