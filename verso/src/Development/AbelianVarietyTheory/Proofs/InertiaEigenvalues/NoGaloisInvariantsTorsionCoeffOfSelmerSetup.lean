import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.NoGlobalInv

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue Λ)]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hl`. Use `haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Establish `h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0`. Rewrite using `[sub_pow_char_pow, ← map_pow, hu]`. Simplify using the standard rewrite rules. Simplify using `using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1`.
-/
theorem sub_one_mem_of_pow {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {l : ℕ} (hp : l.Prime)
    (hl : (l : Λ) ∈ IsLocalRing.maximalIdeal Λ) (u : Λ) {n : ℕ} (hu : u ^ (l ^ n) = 1) :
    u - 1 ∈ IsLocalRing.maximalIdeal Λ := by
  haveI := Fact.mk hp
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue Λ)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hu]; simp
  simpa using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx`. Consider the case `succ n ih`. Introduce `x hS hx h`.

Distinguish the cases in `h1 : ∀ a ∈ I, a • x = 0`. Conclude with `⟨x, hS, hx, h1⟩`. Use `push Not at h1`. Take `⟨a, ha, hax⟩` from `h1`. Use `ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Conclude with `h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)`.
-/
theorem exists_socle {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] (I : Ideal Λ) (S : Submodule Λ M) :
    ∀ (n : ℕ) (x : M), x ∈ S → x ≠ 0 → (∀ a ∈ I ^ n, a • x = 0) →
      ∃ y ∈ S, y ≠ 0 ∧ ∀ a ∈ I, a • y = 0 := by
  intro n
  induction n with
  | zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx
  | succ n ih =>
    intro x hS hx h
    by_cases h1 : ∀ a ∈ I, a • x = 0
    · exact ⟨x, hS, hx, h1⟩
    push Not at h1
    obtain ⟨a, ha, hax⟩ := h1
    refine ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_
    rw [smul_smul]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

/- English proof (translation)
Establish `key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O, A.map (IsLocalRing.residue O) = M ∧ ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p`. Introduce `M`. Establish `hM : M ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g).map (IsLocalRing.residue O))` using `hρ ▸ Submodule.mem_top`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem M h => obtain ⟨g, rfl⟩ := h`.

Conclude with `⟨ρ g, rfl, hs g⟩`. Consider the case `zero => exact ⟨0, by ext; simp, 0, by simp⟩`. Consider the case `add M M' _ _ h h'`. Take `⟨A, rfl, c, hc⟩` from `h`. Take `⟨A', rfl, c', hc'⟩` from `h'`.

Use `⟨A + A', by ext; simp, c + c', fun p => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, map_add, add_smul, Finset.sum_add_distrib, hc, hc']`. Consider the case `smul t M _ h`. Take `⟨A, rfl, c, hc⟩` from `h`. Take `⟨t, rfl⟩` from `IsLocalRing.residue_surjective t`.

Use `⟨t • A, by ext; simp, t * c, fun p => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]`. Establish `key2 : ∀ A : Matrix (Fin r) (Fin r) O, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p`. Introduce `A`. Take `⟨A', hA, c, hc⟩` from `key (A.map (IsLocalRing.residue O))`.

Use `⟨c, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `: A p q - A' p q ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`.

Conclude with `(congrFun (congrFun hA p) q).symm`. Use `hx _ this q` as an intermediate fact. Rewrite `this` using `[map_sub, sub_smul, sub_eq_zero]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `b`. Use `haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr`.

Take `⟨a, hab⟩` from `exists_ne b`. Take `⟨c, hc⟩` from `key2 (Matrix.single a b 1)`. Take `⟨c', hc'⟩` from `key2 (Matrix.single b b 1)`. Establish `h1` using `hc a`. Establish `h2` using `hc' a`.

Establish `h3` using `hc' b`. Simplify using `[Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3`. Rewrite using `[Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]`.
-/
theorem eq_zero_of_span {Γ O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ → Matrix (Fin r) (Fin r) O)
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) = ⊤)
    (x : Fin r → B) (hx : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ j, algebraMap O Λ a • x j = 0)
    (hs : ∀ g, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (ρ g p q) • x q = algebraMap O Λ c • x p) : x = 0 := by
  classical
  have key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (IsLocalRing.residue O) = M ∧
        ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro M
    have hM : M ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) := hρ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M h => obtain ⟨g, rfl⟩ := h; exact ⟨ρ g, rfl, hs g⟩
    | zero => exact ⟨0, by ext; simp, 0, by simp⟩
    | add M M' _ _ h h' =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨A', rfl, c', hc'⟩ := h'
      refine ⟨A + A', by ext; simp, c + c', fun p => ?_⟩
      simp only [Matrix.add_apply, map_add, add_smul, Finset.sum_add_distrib, hc, hc']
    | smul t M _ h =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      refine ⟨t • A, by ext; simp, t * c, fun p => ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]
  have key2 : ∀ A : Matrix (Fin r) (Fin r) O,
      ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro A
    obtain ⟨A', hA, c, hc⟩ := key (A.map (IsLocalRing.residue O))
    refine ⟨c, fun p => ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : A p q - A' p q ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrFun (congrFun hA p) q).symm
    have := hx _ this q
    rwa [map_sub, sub_smul, sub_eq_zero] at this
  funext b
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨a, hab⟩ := exists_ne b
  obtain ⟨c, hc⟩ := key2 (Matrix.single a b 1)
  obtain ⟨c', hc'⟩ := key2 (Matrix.single b b 1)
  have h1 := hc a
  have h2 := hc' a
  have h3 := hc' b
  simp [Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3
  rw [Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]

/- English proof (translation)
Establish `hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ` using `fun a ha hu => ha (hloc.map_nonunit a hu)`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Use `choose n hn using fun j => hB (x j)`.

Take `⟨y, hy, hy0, hym⟩` from `exists_socle (IsLocalRing.maximalIdeal Λ) _ (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j => hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))`. Use `hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)` and prove the remaining obligations. Establish `hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q` using `fun q => by`. Use `congrFun (hym _ (hκ g)) q` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p` using `congrFun (hy g) p`. Rewrite using `[← hg, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]`. Use `congr 2`.

Simplify using `[twGL, scalGL, Matrix.diagonal_mul]`.
-/
theorem invariants_eq_bot {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ)
    (κ : Γ →* Λˣ) (hloc : IsLocalHom (algebraMap O Λ))
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (hκ : ∀ g, ((κ g : Λˣ) : Λ) - 1 ∈ IsLocalRing.maximalIdeal Λ) (hB : Tors Λ B) :
    (repOn (twGL ρ χ) κ B).invariants = ⊥ := by
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ :=
    fun a ha hu => ha (hloc.map_nonunit a hu)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  choose n hn using fun j => hB (x j)
  obtain ⟨y, hy, hy0, hym⟩ := exists_socle (IsLocalRing.maximalIdeal Λ) _
    (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j =>
      hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))
  refine hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y
    (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)
  have hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q := fun q => by
    have := congrFun (hym _ (hκ g)) q
    rwa [Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero] at this
  have hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p :=
    congrFun (hy g) p
  rw [← hg, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]
  congr 2
  simp [twGL, scalGL, Matrix.diagonal_mul]

/- English proof (translation)
Introduce `B _ _ _ _ hB`. Establish `hloc` using `h.2.1`. Establish `hr : 100 ≤ D.R.r` using `h.1.2.2.2.2.2.2`. Establish `hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i)` using `fun hu => X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))`. Establish `hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ` using `fun hu => hl0 (hloc.map_nonunit _ (by simpa using hu))`.

Use `invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB` and prove the remaining obligations. Take `⟨m, hgm⟩` from `h.2.2.2.2.1 g`. Conclude with `sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m) (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])`.
-/
theorem noInv (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) (h : Setup bkP i s κ Q) : NoInv i s κ := by
  intro B _ _ _ _ hB
  have hloc := h.2.1
  have hr : 100 ≤ D.R.r := h.1.2.2.2.2.2.2
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ := fun hu =>
    hl0 (hloc.map_nonunit _ (by simpa using hu))
  refine invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB
  obtain ⟨m, hgm⟩ := h.2.2.2.2.1 g
  exact sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m)
    (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])

end GlobalTheory.NoGlobalInv
