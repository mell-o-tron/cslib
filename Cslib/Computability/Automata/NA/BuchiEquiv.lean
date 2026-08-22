/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Equivalence of nondeterministic Buchi automata (NBAs). -/

@[expose] public section

universe u v w

namespace Cslib.Automata.NA.Buchi

open Set Function Filter ωSequence ωLanguage ωAcceptor
open scoped LTS

variable {Symbol : Type u} {State : Type v} {State' : Type w}

/-- Lifts an equivalence on states to an equivalence on NBAs. -/
@[scoped grind =]
def reindex (f : State ≃ State') : Buchi State Symbol ≃ Buchi State' Symbol where
  toFun nba := {
    Tr s x t := nba.Tr (f.symm s) x (f.symm t)
    start := f '' nba.start
    accept := f.symm ⁻¹' nba.accept
  }
  invFun nba' := {
    Tr s x t := nba'.Tr (f s) x (f t)
    start := f.symm '' nba'.start
    accept := f ⁻¹' nba'.accept
  }
  left_inv nba := by simp
  right_inv nba' := by simp

theorem reindex_run_iff {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss' : ωSequence State'} :
    (nba.reindex f).Run xs ss' ↔ nba.Run xs (ss'.map f.symm) := by
  constructor
  · rintro ⟨h_init, h_next⟩
    exact ⟨mem_image_equiv.mp  h_init, fun n ↦ h_next n⟩
  · rintro ⟨h_init, h_next⟩
    exact ⟨mem_image_equiv.mpr h_init, fun n ↦ h_next n⟩

@[simp]
theorem reindex_run_iff' {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss : ωSequence State} :
    (nba.reindex f).Run xs (ss.map f) ↔ nba.Run xs ss := by
  simp [reindex_run_iff]

@[simp, scoped grind =]
theorem reindex_language_eq {f : State ≃ State'} {nba : Buchi State Symbol} :
    language (nba.reindex f) = language nba := by
  apply mem_ext
  intro xs
  constructor
  · rintro ⟨ss', h_run', h_acc'⟩
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    simp only [mem_language, Accepts]
    exact frequently_principal.mp (· (reindex_run_iff.mp h_run') h_acc')
  · rintro ⟨ss, h_run, h_acc⟩
    use ss.map f
    constructor <;> grind [reindex_run_iff']

@[simp, scoped grind =]
def ωLanguageEquivalent [ωAcceptor A Symbol] [ωAcceptor B Symbol] (n1 : A) (n2 : B) : Prop :=
  language n1 = language n2

notation:50 p " ≈ " q => (ωLanguageEquivalent p q)

open scoped Classical in
/-- builds an nba which accepts the same language as the gnba -/
noncomputable def gnba_to_nba (g : GBuchi State Symbol) [NeZero g.accept.card] :
  Buchi (State × Fin (g.accept.card)) Symbol :=
  {
    Tr := (fun x y z =>
      g.Tr x.fst y z.fst ∧
      (z.snd =
        if x.fst ∈ (((Finset.equivFin g.accept).symm (x.snd)).val)
        then (x.snd + 1) % g.accept.card
        else x.snd)),
    start := { x | x.fst ∈ g.start ∧ x.snd = 0 },
    accept := { x | x.fst ∈ ((Finset.equivFin g.accept).symm (x.snd)).val }
  }

open scoped Classical in
private theorem counter_not_eventually_const {N : ℕ} [NeZero N]
    {c : ℕ → Fin N} {A : ℕ → Prop}
    (hN : N > 1)
    (hstep : ∀ k, c (k + 1) = if A k then (c k + 1) % N else c k)
    (hfreq : ∃ᶠ k in atTop, A k) (j : Fin N) :
    ¬ ∃ m, ∀ k ≥ m, c k = j := by
    simp only [ge_iff_le, not_exists, not_forall, exists_prop]
    have hc := hfreq.forall_exists_of_atTop
    intro z
    have hz := hc z
    obtain ⟨hp, p⟩ := hz
    rcases eq_or_ne (c hp) j with h_eq | h_neq
    · use hp + 1
      constructor
      · have _ := p.left
        omega
      · intro a
        have habs := hstep hp
        rw [a, ite_eq_left p.right] at habs
        rcases eq_or_ne (c hp) j with h_eq | h_neq
        · rw [h_eq] at habs
          have hjN : (j : ℕ) < N := j.isLt
          rcases Nat.eq_or_lt_of_le (hjN) with h | h
          · rw [← Nat.succ_eq_add_one] at habs
            rw [h] at habs
            simp only [Nat.mod_self, Fin.val_eq_zero_iff] at habs
            rw [habs] at h
            simp at h
            omega
          · rw [Nat.mod_eq_of_lt h] at habs
            omega
        · omega
    · use hp
      constructor
      · exact p.left
      · exact h_neq

open scoped Classical in
private theorem step {N : ℕ} [NeZero N]
    {c : ℕ → Fin N} {A : ℕ → Prop}
    (hN : N > 1) (p : Fin N)
    (hstep : ∀ k, c (k + 1) = if A k then (c k + 1) % N else c k)
    (hfreq : ∃ᶠ k in atTop, A k)
    (hfreqj : ∃ᶠ j in atTop, (c j) = p) :
    ∀ t: ℕ, ∃ᶠ k in atTop, c k = (p + t) % N := by
    intro t
    induction t with
    | zero =>
      simp only [add_zero]
      rw [Nat.mod_eq_of_lt]
      · exact hfreqj.mono fun j hj => congrArg Fin.val hj
      · exact p.isLt
    | succ t ih =>
      intro x
      have exlimit := mem_atTop_sets.mp x
      obtain ⟨h, hp⟩ := exlimit
      simp only [mem_ofPred_eq] at hp
      have z := Filter.frequently_atTop.mp ih
      obtain ⟨h1, hp1⟩ := z h
      have counter_hp := counter_not_eventually_const hN hstep hfreq ⟨(↑p + t) % N, by omega⟩
      simp only [ge_iff_le, not_exists, not_forall] at counter_hp
      have w := counter_hp h1
      have q1 := Nat.find_spec w
      have q2 : (Nat.find w - 1) < Nat.find w := by
        grind
      have q3 : h1 ≤ Nat.find w - 1 := by
        grind
      have q4 : 1 ≤ Nat.find w := by
        grind
      have qmin := Nat.find_min w q2
      push Not at qmin
      have qmin' := qmin q3
      have hstep' := hstep (Nat.find w - 1)
      cases Classical.em (A (Nat.find w - 1)) with
      | inl h2 =>
        rw [ite_eq_left h2, qmin', Nat.sub_add_cancel q4, Nat.mod_add_mod] at hstep'
        exact hp (Nat.find w) (by grind) hstep'
      | inr h2 =>
        rw [ite_eq_right h2, qmin', Nat.sub_add_cancel q4] at hstep'
        grind

theorem pigeonhole (hN : N ≥ 1) (c : ℕ → Fin N) : ∃z, ∃ᶠ j in atTop, c j = z := by
  induction N, hN using Nat.le_induction with
  | base =>
    have z : ∀k, c k = 0 := by grind
    by_contra h
    simp only [Fin.exists_fin_one, Fin.isValue, not_frequently, eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    have hb := ha a
    grind
  | succ m hjm ih =>
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := (h ⟨m, by grind⟩).exists_forall_of_atTop
    let c' : ℕ → Fin m := fun k => ⟨c (a + k), by grind⟩
    have hp := ih c'
    obtain ⟨z, hz⟩ := hp
    have w := hz.forall_exists_of_atTop
    have ⟨q, hq⟩ := (h ⟨z, by grind⟩).exists_forall_of_atTop
    have j := w q
    grind

open scoped Classical in
noncomputable def ss' (c : ℕ → State) (g : GBuchi State Symbol) (h_nz : g.accept.card > 0) :
    ℕ → State × Fin g.accept.card
  | 0 => (c 0, ⟨0, h_nz⟩)
  | n + 1 =>
    let rec_call := ss' c g h_nz n
    (c (n + 1),
      if rec_call.1 ∈ ((Finset.equivFin g.accept).symm (rec_call).2).val then
      ⟨(rec_call.2 + 1) % g.accept.card, Nat.mod_lt (rec_call.2 + 1) h_nz⟩ else rec_call.2)

open scoped Classical in
/-- an ωAcceptor with no accepting states, has emptyLanguage -/
theorem gnba_to_nba_equiv :
  ∀ (g : GBuchi State Symbol), ∃ T: Type v,  ∃ n : Buchi T Symbol, n ≈ g := by
  intro g
  rcases Nat.eq_zero_or_pos g.accept.card with h_z | h_nz
  · use State, { g with accept := Set.univ }
    simp only [ωLanguageEquivalent]
    ext xs
    simp only [← mem_def, mem_language]
    apply Iff.intro
    · intro a
      simp only [Accepts]
      simp only [Accepts, mem_univ, frequently_true_iff_neBot, exists_and_right] at a
      obtain ⟨c, hc⟩ := a
      obtain ⟨d, hd⟩ := c
      use d
      constructor
      · exact hd
      grind
    · intro a
      simp only [Accepts, mem_univ, frequently_true_iff_neBot, exists_and_right]
      constructor
      · simp only [Accepts] at a
        obtain ⟨e, he⟩ := a
        use e
        exact he.left
      · exact inferInstance
  · rcases Nat.lt_or_ge 1 g.accept.card with h1 | hn1
    · have : NeZero g.accept.card := NeZero.of_pos h_nz
      use (State × Fin (g.accept.card)), gnba_to_nba g
      have to_transition : ∀ o: ωSequence Symbol, ∀ p: ωSequence (State × Fin g.accept.card),
        (gnba_to_nba g).Run o p → ∀i : ℕ, (p i).snd ≠ (p (i + 1)).snd →
        (p i).fst ∈ (((Finset.equivFin g.accept).symm (p i).snd).val) := by
        intros x y z t
        contrapose
        intro hp
        simp [gnba_to_nba] at z
        have k := (z.trans t).right
        simp [ite_eq_right hp] at k
        grind
      have stay_the_same_or_transition : ∀ j : Fin g.accept.card, ∀ o: ωSequence Symbol,
        ∀ p: ωSequence (State × Fin g.accept.card), (gnba_to_nba g).Run o p  → ∀i : ℕ,
        (p i).snd = j → (∀ z ≥ i, (p z).snd = j) ∨ (∃ q:ℕ, q ≥ i ∧ (p q).snd = j ∧
        (p (q+1)).snd ≠ j) := by
        simp only [ge_iff_le, ne_eq]
        intros a b c d e f
        rcases Classical.em (∃q, e ≤ q ∧ (c q).2 = a ∧ ¬(c (q + 1)).2 = a) with hB | hnB
        · right
          exact hB
        · push Not at hnB
          left
          intros z hz
          induction z, hz using Nat.le_induction with
          | base => exact f
          | succ m hjm ih => grind
      ext x
      simp only [← mem_def, mem_language]
      apply Iff.intro
      · intro a
        simp only [Accepts]
        simp only [Accepts] at a
        obtain ⟨c, hc⟩ := a
        use { get := fun i => (c i).fst }
        constructor
        · constructor
          · simp only [get_fun]
            simp only [gnba_to_nba, mem_ofPred_eq] at hc
            have h1 := hc.left.start
            simp at h1
            exact h1.left
          · intro j
            simp only [get_fun]
            have h1 := hc.left.trans
            simp only [gnba_to_nba, LTS.OmegaExecution] at h1
            obtain ⟨h_tr, _⟩ := h1 j
            exact h_tr
        · intros f fa
          let funz : ℕ → Fin g.accept.card := fun k => (c k).2
          let A : ℕ → Prop := fun k => (c k).1 ∈ ((Finset.equivFin g.accept).symm ((c k).2)).val
          have hstep : ∀ k, funz (k + 1) = (if A k then (funz k + 1) % g.accept.card else funz k) :=
          by
            intro t
            split_ifs with hA
            · unfold funz
              unfold A at hA
              have hc' := hc.left
              have hc'' := hc'.trans t
              simp [gnba_to_nba] at hc''
              have hc''' := hc''.right
              rw [ite_eq_left hA] at hc'''
              exact hc'''
            · unfold funz
              unfold A at hA
              have hc' := hc.left
              have hc'' := hc'.trans t
              simp [gnba_to_nba] at hc''
              have hc''' := hc''.right
              rw [ite_eq_right hA] at hc'''
              exact hc'''
          have hfreq : ∃ᶠ k in atTop, A k := by
            intro j
            obtain ⟨p, hp⟩ := j.exists_forall_of_atTop
            have hp1 := hc.right
            rw [gnba_to_nba] at hp1
            simp only [mem_ofPred_eq] at hp1
            exact hp1 j
          obtain ⟨t, hfreqj⟩ : ∃t, ∃ᶠ j in atTop, funz j = t := pigeonhole h_nz funz
          have hfundamental := step h1 t hstep hfreq hfreqj
          intro a
          have hp' := a.exists_forall_of_atTop
          simp only [get_fun] at hp'
          obtain ⟨d, hd⟩ := hp'
          let index := ((Finset.equivFin g.accept) ⟨f, fa⟩)
          rcases Nat.le_or_ge t index with hle | hge
          · have idk := ((hfundamental (index - t)).forall_exists_of_atTop d)
            obtain ⟨e, he⟩ := idk
            simp [hle, funz, Nat.mod_eq_of_lt index.isLt] at he
            have stsot := stay_the_same_or_transition index x c hc.left e (Fin.ext he.right)
            rcases stsot with h1 | h2
            · obtain ⟨hc_r, hp_hc_r⟩ := hc.right.forall_exists_of_atTop e
              simp only [gnba_to_nba, mem_ofPred_eq] at hp_hc_r
              rw [h1 hc_r] at hp_hc_r
              · grind
              · exact hp_hc_r.left
            · obtain ⟨h2, hp_h2⟩ := h2
              have tt := to_transition x c hc.left h2 (by omega)
              rw [hp_h2.right.left] at tt
              grind
          · have idk2 := ((hfundamental (g.accept.card + index - t)).forall_exists_of_atTop d)
            rw [Nat.add_comm t (g.accept.card + index - t), Nat.sub_add_cancel (by omega),
              Nat.add_mod_left]
            at idk2
            obtain ⟨e, he⟩ := idk2
            simp [funz, Nat.mod_eq_of_lt index.isLt] at he
            have stsot := stay_the_same_or_transition index x c hc.left e (Fin.ext he.right)
            rcases stsot with h1 | h2
            · obtain ⟨hc_r, hp_hc_r⟩ := hc.right.forall_exists_of_atTop e
              simp only [gnba_to_nba, mem_ofPred_eq] at hp_hc_r
              rw [h1 hc_r hp_hc_r.left] at hp_hc_r
              grind
            · obtain ⟨h2, hp_h2⟩ := h2
              have tt := to_transition x c hc.left h2 (by omega)
              rw [hp_h2.right.left] at tt
              grind
      · intro a
        simp only [Accepts]
        simp only [Accepts] at a
        obtain ⟨c, hc⟩ := a
        let ss : ωSequence (State × Fin g.accept.card) := ss' c g h_nz
        use ss
        have is_a_valid_run : (gnba_to_nba g).Run x ss := by
          simp only [gnba_to_nba]
          constructor
          · dsimp [ss, ss']
            constructor
            · exact hc.left.start
            · omega
          · intro j
            constructor
            · cases j with
              | zero =>
                dsimp [ss, ss']
                exact hc.left.trans 0
              | succ n =>
                dsimp [ss, ss']
                exact hc.left.trans (n + 1)
            · split
              · dsimp [ss, ss']
                grind
              · dsimp [ss, ss']
                grind
        constructor
        · exact is_a_valid_run
        · intro a
          obtain ⟨b, hb⟩ := a.exists_forall_of_atTop
          have cast_gnba_to_nba : ∀x, (c x) = (ss x).fst := by
            intro x
            cases x with
            | zero => dsimp [ss, ss']
            | succ n => dsimp [ss, ss']
          let st_at_b := ss b
          let set_at_b := ((Finset.equivFin g.accept).symm ((st_at_b).2)).val
          have stsot := stay_the_same_or_transition st_at_b.snd x ss is_a_valid_run b (by grind)
          rcases stsot with h_const | h_nconst
          · have hc_r := (hc.right set_at_b
              ((Finset.equivFin g.accept).symm ((st_at_b).2)).val_prop).forall_exists_of_atTop b
            obtain ⟨w_hc_r, hp_hc_r⟩ := hc_r
            have hb_abs := hb w_hc_r hp_hc_r.left
            have hp : ss w_hc_r ∈ (gnba_to_nba g).accept := by
              rw [gnba_to_nba]
              simp only [mem_ofPred_eq, h_const w_hc_r hp_hc_r.left, ← cast_gnba_to_nba]
              exact hp_hc_r.right
            exact hb_abs hp
          · obtain ⟨w_h_nconst, hp_h_nconst⟩ := h_nconst
            have tt := to_transition x ss is_a_valid_run w_h_nconst
              (by rw [hp_h_nconst.right.left]
                  exact hp_h_nconst.right.right.symm)
            exact hb w_h_nconst hp_h_nconst.left tt
    · have card_1 : g.accept.card = 1 := by omega
      obtain ⟨f, hf⟩ := Finset.card_eq_one.mp card_1
      use State, { g with accept := f }
      have hacc : ∀ y : ωSequence State,
      (∀ F ∈ g.accept, ∃ᶠ k in atTop, y k ∈ F) ↔ ∃ᶠ k in atTop, y k ∈ f := by
        intro y
        simp [hf]
      ext x
      simp only [language, Accepts, hacc]





end Cslib.Automata.NA.Buchi
