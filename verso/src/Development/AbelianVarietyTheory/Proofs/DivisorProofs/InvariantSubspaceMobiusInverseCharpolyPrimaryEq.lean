import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLe
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusInversionAffineFinrankSubspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalApplyMem

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.Primary

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (π.domRestrict (A.comap π))`. Rewrite `h` using `[LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hπ, LinearMap.ker_domRestrict, (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap π)).finrank_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_comap_of_surjective {F V U : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup U] [Module F U] (π : V →ₗ[F] U) (hπ : Function.Surjective π)
    (A : Submodule F U) :
    Module.finrank F (A.comap π) = Module.finrank F (LinearMap.ker π) + Module.finrank F A := by
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (A.comap π))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hπ, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap π)).finrank_eq] at h
  omega

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Use `hs 1 1 monic_one monic_one` as an intermediate fact. Rewrite `this` using `[mul_one]`. Simplify using `using this`.

Consider the case `succ j ih => rw [pow_succ, hs _ _ (hf.pow j) hf, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem additive_pow {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]} (hf : f.Monic)
    (j : ℕ) : s (f ^ j) = j * s f := by
  induction j with
  | zero =>
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    simpa using this
  | succ j ih => rw [pow_succ, hs _ _ (hf.pow j) hf, ih]; push_cast; ring

/- English proof (translation)
Establish `h1 : LinearMap.charpoly (g.restrict hA) ∣ f ^ m` using `hc ▸ ⟨_, charpoly_eq_restrict_mul_mapQ A g hA⟩`. Take `⟨j, -, hj⟩` from `(dvd_prime_pow hi.prime m).1 h1`. Establish `h2 : LinearMap.charpoly (g.restrict hA) = f ^ j` using `eq_of_monic_of_associated (LinearMap.charpoly_monic _) (hf.pow j) hj`. Establish `h3` using `LinearMap.charpoly_natDegree (g.restrict hA)`. Rewrite `h3` using `[h2, hf.natDegree_pow]`.

Rewrite using `[h2, additive_pow hs hf, ← h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem additive_restrict {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s : F[X] → ℂ} (hs : IsAdditive s) {g : Module.End F V} {f : F[X]} {m : ℕ} (hf : f.Monic)
    (hi : Irreducible f) (hc : LinearMap.charpoly g = f ^ m) (A : Submodule F V) (hA : ∀ x ∈ A, g x ∈ A) :
    (f.natDegree : ℂ) * s (LinearMap.charpoly (g.restrict hA)) = (Module.finrank F A : ℂ) * s f := by
  have h1 : LinearMap.charpoly (g.restrict hA) ∣ f ^ m :=
    hc ▸ ⟨_, charpoly_eq_restrict_mul_mapQ A g hA⟩
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hi.prime m).1 h1
  have h2 : LinearMap.charpoly (g.restrict hA) = f ^ j :=
    eq_of_monic_of_associated (LinearMap.charpoly_monic _) (hf.pow j) hj
  have h3 := LinearMap.charpoly_natDegree (g.restrict hA)
  rw [h2, hf.natDegree_pow] at h3
  rw [h2, additive_pow hs hf, ← h3]
  push_cast; ring

/- English proof (translation)
Establish `hp : ∀ (j : ℕ), ∀ x ∈ W, (N ^ j) x ∈ W`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro x hx`. Simplify using `using hx`.

Consider the case `succ j ih => intro x hx`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hW x hx)`. Establish `key : ∀ (j : ℕ) (v : V), ∃ w ∈ W, ∃ u, v = w + (N ^ j) u`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro v; exact ⟨0, W.zero_mem, v, by simp⟩`. Consider the case `succ j ih`. Introduce `v`. Take `⟨w, hw, u, rfl⟩` from `ih v`.

Take `⟨w', hw', u', rfl⟩` from `h u`. Use `⟨w + (N ^ j) w', W.add_mem hw (hp j w' hw'), u', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, pow_succ, Module.End.mul_apply, add_assoc]`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Take `⟨w, hw, u, rfl⟩` from `key m v`.

Simplify `hw` using `[hN]`.
-/
theorem eq_top_of_nilpotent {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : Module.End F V)
    {m : ℕ} (hN : N ^ m = 0) (W : Submodule F V) (hW : ∀ x ∈ W, N x ∈ W)
    (h : ∀ v, ∃ w ∈ W, ∃ u, v = w + N u) : W = ⊤ := by
  have hp : ∀ (j : ℕ), ∀ x ∈ W, (N ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih => intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hW x hx)
  have key : ∀ (j : ℕ) (v : V), ∃ w ∈ W, ∃ u, v = w + (N ^ j) u := by
    intro j
    induction j with
    | zero => intro v; exact ⟨0, W.zero_mem, v, by simp⟩
    | succ j ih =>
      intro v
      obtain ⟨w, hw, u, rfl⟩ := ih v
      obtain ⟨w', hw', u', rfl⟩ := h u
      refine ⟨w + (N ^ j) w', W.add_mem hw (hp j w' hw'), u', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨w, hw, u, rfl⟩ := key m v
  simpa [hN] using hw

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem`. Consider the case `exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem`. Consider the case `(apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem ..)`.
-/
theorem aeval_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) : ∀ x ∈ W, aeval g p x ∈ W := by
  first
  | exact @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | (apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem ..)

/- English proof (translation)
Establish `key : ∀ (p : F[X]) (v : V), π (aeval g p v) = AdjoinRoot.mk f p • π v`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a`. Introduce `v`.

Rewrite using `[AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, algebraMap_smul]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => intro v`. Simplify using `[hp, hq, add_smul]`. Consider the case `monomial n a h`.

Introduce `v`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h, hπ, map_mul (AdjoinRoot.mk f) _ X, AdjoinRoot.mk_X, smul_smul]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, W.zero_mem, map_zero _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨w, hw, rfl⟩` from `hx`. Take `⟨w', hw', rfl⟩` from `hy`. Conclude with `⟨w + w', W.add_mem hw hw', map_add _ _ _⟩`. Consider the case `smul k x _ hx`.

Take `⟨w, hw, rfl⟩` from `hx`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective k`. Conclude with `⟨_, aeval_mem g W hW p w hw, key p w⟩`.
-/
theorem mem_image_of_mem_span {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (f : F[X]) {t : ℕ} (π : V →ₗ[F] (Fin t → AdjoinRoot f)) (hπ : ∀ v, π (g v) = AdjoinRoot.root f • π v)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (y : Fin t → AdjoinRoot f)
    (hy : y ∈ Submodule.span (AdjoinRoot f) (π '' W)) : ∃ w ∈ W, π w = y := by
  have key : ∀ (p : F[X]) (v : V), π (aeval g p v) = AdjoinRoot.mk f p • π v := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro v
      rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, algebraMap_smul]
      simp
    | add p q hp hq => intro v; simp [hp, hq, add_smul]
    | monomial n a h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h, hπ, map_mul (AdjoinRoot.mk f) _ X,
        AdjoinRoot.mk_X, smul_smul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, W.zero_mem, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', W.add_mem hw hw', map_add _ _ _⟩
  | smul k x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective k
    exact ⟨_, aeval_mem g W hW p w hw, key p w⟩

end GlobalTheory.CuspGL.Primary

namespace GlobalTheory.CuspGL

open Primary in

/- English proof (translation)
Introduce `F _ _ V _ _ _ s hs g f m t hf hi hm hc ht`. Use `haveI : Fact (Irreducible f) := ⟨hi⟩`. Establish `he : 0 < f.natDegree` using `hi.natDegree_pos`. Establish `he' : (f.natDegree : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Take `⟨t', π, hsurj, hπ, hker, ht'⟩` from `GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' F V g f`.

Take `rfl : t' = t` from `Nat.eq_of_mul_eq_mul_left he (ht'.symm.trans ht)`. Use `haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite`. Establish `hK : Module.finrank F (AdjoinRoot f) = f.natDegree` using `(AdjoinRoot.powerBasis hi.ne_zero).finrank`. Use `haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F`. Establish `hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree`.

Rewrite using `[← hK]`. Conclude with `Module.natCard_eq_pow_finrank`. Establish `hN : (aeval g f) ^ m = 0` using `by rw [← map_pow, ← hc, LinearMap.aeval_self_charpoly]`. Establish `nak : ∀ W : Submodule F V, (∀ x ∈ W, g x ∈ W) → Submodule.span (AdjoinRoot f) (π '' W) = ⊤ → W = ⊤`. Introduce `W hW h`.

Use `eq_top_of_nilpotent (aeval g f) hN W (aeval_mem g W hW f) fun v => ?_` and prove the remaining obligations. Take `⟨w, hw, hw'⟩` from `mem_image_of_mem_span g f π hπ W hW (π v) (h ▸ Submodule.mem_top)`. Establish `: v - w ∈ LinearMap.ker π` using `by rw [LinearMap.mem_ker, map_sub, hw', sub_self]`. Rewrite `this` using `[hker]`. Take `⟨u, hu⟩` from `this`.

Conclude with `⟨w, hw, u, by rw [hu]; abel⟩`. Establish `htpos : 0 < t'`. Break down `Nat.eq_zero_or_pos t' with rfl | h` into its components or cases. It suffices to derive a contradiction. Establish `h1` using `nak ⊥ (by simp) (Subsingleton.elim _ _)`.

Establish `h2` using `LinearMap.charpoly_natDegree g`. Rewrite `h2` using `[hc, hf.natDegree_pow, ← finrank_top, ← h1, finrank_bot]`. Conclude with `(Nat.mul_pos hm he).ne' h2`. Conclude with `h`. Use `haveI : Finite V := Module.finite_of_finite F`.

Use `haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective`. Use `haveI : Finite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)) := Finite.of_injective _ SetLike.coe_injective`. Use `letI := Fintype.ofFinite (Submodule F V)`. Use `letI := Fintype.ofFinite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f))`. Set `P : Submodule F V → ℂ` to `fun W => if h : ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h) else 0`.

Set `Φ : Submodule F V → Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)` to `fun W => Submodule.span (AdjoinRoot f) (π '' W)`. Set `G : Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) → ℂ` to `fun B => ∑ W ∈ Finset.univ.filter (fun W => Φ W = B), P W`. Establish `hrk : Module.finrank (AdjoinRoot f) (Fin t' → AdjoinRoot f) = t'` using `by simp`. Establish `main` using `GlobalTheory.T.mobiusInversion_affine_finrank_subspaces (AdjoinRoot f) (Fin t' → AdjoinRoot f) G ((Module.finrank F (LinearMap.ker π) : ℂ) * s f / f.natDegree) (s f) (by rw [hrk]; exact htpos) (by`. Introduce `A`.

Establish `hA : ∀ x ∈ (A.restrictScalars F).comap π, g x ∈ (A.restrictScalars F).comap π`. Introduce `x hx`. Rewrite `hx`, the goal using `[Submodule.mem_comap, Submodule.restrictScalars_mem]`. Rewrite using `[hπ]`. Conclude with `A.smul_mem _ hx`.

Establish `hle : ∀ W, Φ W ≤ A ↔ W ≤ (A.restrictScalars F).comap π` using `fun W => by`. Rewrite using `[Submodule.span_le, Set.image_subset_iff]`. Both sides reduce to the same expression. Establish `h1` using `finsum_psi_le F V s _ g hA`. Establish `h2` using `additive_restrict hs hf hi hc _ hA`.

Rewrite `h2` using `[finrank_comap_of_surjective π hsurj]`. Establish `h3 : Module.finrank F (A.restrictScalars F) = f.natDegree * Module.finrank (AdjoinRoot f) A`. Rewrite using `[← hK, Module.finrank_mul_finrank]`. Both sides reduce to the same expression. Rewrite `h2` using `[h3]`.

Establish `h4 : ∑ᶠ B : {B // B ≤ A}, G B.1 = ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W`. Rewrite using `[finsum_eq_sum_of_fintype, ← Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ A)) (by simp) G, Finset.sum_fiberwise_eq_sum_filter]`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `W`. Simplify using `[hle]`.

Establish `h5 : ∑ᶠ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W`. Establish `: ∀ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = P W.1` using `fun W => by simp only [P]; rw [dif_pos W.2.2]`. Rewrite using `[finsum_congr this, finsum_eq_sum_of_fintype, ← Finset.sum_subtype (Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W)) (by simp) P]`. Use `Finset.sum_subset (fun W => by simp; tauto) fun W hW hW' => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'`.

Conclude with `dif_neg fun h => hW' ⟨hW, h⟩`. Rewrite using `[h4, ← h5, h1]`. Move the coercions through the operations in `at h2`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h2)`.

Establish `hG : G ⊤ = psi s V g`. Establish `htop : ∀ x ∈ (⊤ : Submodule F V), g x ∈ (⊤ : Submodule F V)` using `fun _ _ => trivial`. Establish `h1 : G ⊤ = P ⊤`. Use `Finset.sum_eq_single_of_mem ⊤ ?_ fun W hW hW' => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Φ]`.

Rewrite using `[Submodule.top_coe, Set.image_univ, hsurj.range_eq, Submodule.span_univ]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hW`. Conclude with `dif_neg fun h => hW' (nak W h hW)`. Rewrite using `[h1]`. Simplify using `only [P]`.

Rewrite using `[dif_pos htop, ← psi_conj F s _ _ Submodule.topEquiv]`. Use `congr 1`. Rewrite using `[← hG, main, hrk, hcard]`. Simplify using `only [Nat.cast_pow, ← pow_mul]`.
-/
theorem psi_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  intro F _ _ V _ _ _ s hs g f m t hf hi hm hc ht
  classical
  haveI : Fact (Irreducible f) := ⟨hi⟩
  have he : 0 < f.natDegree := hi.natDegree_pos
  have he' : (f.natDegree : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  obtain ⟨t', π, hsurj, hπ, hker, ht'⟩ := GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' F V g f
  obtain rfl : t' = t := Nat.eq_of_mul_eq_mul_left he (ht'.symm.trans ht)
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hK : Module.finrank F (AdjoinRoot f) = f.natDegree := (AdjoinRoot.powerBasis hi.ne_zero).finrank
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree := by
    rw [← hK]; exact Module.natCard_eq_pow_finrank
  have hN : (aeval g f) ^ m = 0 := by rw [← map_pow, ← hc, LinearMap.aeval_self_charpoly]
  have nak : ∀ W : Submodule F V, (∀ x ∈ W, g x ∈ W) →
      Submodule.span (AdjoinRoot f) (π '' W) = ⊤ → W = ⊤ := by
    intro W hW h
    refine eq_top_of_nilpotent (aeval g f) hN W (aeval_mem g W hW f) fun v => ?_
    obtain ⟨w, hw, hw'⟩ := mem_image_of_mem_span g f π hπ W hW (π v) (h ▸ Submodule.mem_top)
    have : v - w ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_sub, hw', sub_self]
    rw [hker] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨w, hw, u, by rw [hu]; abel⟩
  have htpos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with rfl | h
    · exfalso
      have h1 := nak ⊥ (by simp) (Subsingleton.elim _ _)
      have h2 := LinearMap.charpoly_natDegree g
      rw [hc, hf.natDegree_pow, ← finrank_top, ← h1, finrank_bot] at h2
      exact (Nat.mul_pos hm he).ne' h2
    · exact h
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)) :=
    Finite.of_injective _ SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F V)
  letI := Fintype.ofFinite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f))
  let P : Submodule F V → ℂ := fun W => if h : ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h) else 0
  let Φ : Submodule F V → Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) :=
    fun W => Submodule.span (AdjoinRoot f) (π '' W)
  let G : Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) → ℂ :=
    fun B => ∑ W ∈ Finset.univ.filter (fun W => Φ W = B), P W
  have hrk : Module.finrank (AdjoinRoot f) (Fin t' → AdjoinRoot f) = t' := by simp
  have main := GlobalTheory.T.mobiusInversion_affine_finrank_subspaces (AdjoinRoot f) (Fin t' → AdjoinRoot f) G
    ((Module.finrank F (LinearMap.ker π) : ℂ) * s f / f.natDegree) (s f) (by rw [hrk]; exact htpos) (by
      intro A
      have hA : ∀ x ∈ (A.restrictScalars F).comap π, g x ∈ (A.restrictScalars F).comap π := by
        intro x hx
        rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
        rw [hπ]; exact A.smul_mem _ hx
      have hle : ∀ W, Φ W ≤ A ↔ W ≤ (A.restrictScalars F).comap π := fun W => by
        rw [Submodule.span_le, Set.image_subset_iff]; rfl
      have h1 := finsum_psi_le F V s _ g hA
      have h2 := additive_restrict hs hf hi hc _ hA
      rw [finrank_comap_of_surjective π hsurj] at h2
      have h3 : Module.finrank F (A.restrictScalars F) = f.natDegree * Module.finrank (AdjoinRoot f) A := by
        rw [← hK, Module.finrank_mul_finrank]; rfl
      rw [h3] at h2
      have h4 : ∑ᶠ B : {B // B ≤ A}, G B.1 =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        rw [finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ A)) (by simp) G,
          Finset.sum_fiberwise_eq_sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext W; simp [hle]
      have h5 : ∑ᶠ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        have : ∀ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) = P W.1 := fun W => by simp only [P]; rw [dif_pos W.2.2]
        rw [finsum_congr this, finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter
            (fun W => W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W)) (by simp) P]
        refine Finset.sum_subset (fun W => by simp; tauto) fun W hW hW' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'
        exact dif_neg fun h => hW' ⟨hW, h⟩
      rw [h4, ← h5, h1]
      push_cast at h2
      field_simp
      linear_combination h2)
  have hG : G ⊤ = psi s V g := by
    have htop : ∀ x ∈ (⊤ : Submodule F V), g x ∈ (⊤ : Submodule F V) := fun _ _ => trivial
    have h1 : G ⊤ = P ⊤ := by
      refine Finset.sum_eq_single_of_mem ⊤ ?_ fun W hW hW' => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Φ]
        rw [Submodule.top_coe, Set.image_univ, hsurj.range_eq, Submodule.span_univ]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
        exact dif_neg fun h => hW' (nak W h hW)
    rw [h1]
    simp only [P]
    rw [dif_pos htop, ← psi_conj F s _ _ Submodule.topEquiv]
    congr 1
  rw [← hG, main, hrk, hcard]
  simp only [Nat.cast_pow, ← pow_mul]

end GlobalTheory.CuspGL
