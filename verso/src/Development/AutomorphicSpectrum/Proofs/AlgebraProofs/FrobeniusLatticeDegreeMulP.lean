import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement

noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFrob

variable {K : Type} [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]

/- English proof (translation)
Use `haveI : ExpChar K p := ExpChar.prime Fact.out`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, ← frobenius_def, RingHom.map_det]`. Use `congr 1`.
-/
theorem det_frobVec {d : ℕ} (b : Fin d → Fin d → K) :
    (Pi.basisFun K (Fin d)).det (fun q => frobVec p (b q)) =
      ((Pi.basisFun K (Fin d)).det b) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [Module.Basis.det_apply, Module.Basis.det_apply, ← frobenius_def, RingHom.map_det]
  congr 1

/- English proof (translation)
Establish `hnd : n = d`. Establish `h` using `Module.finrank_eq_card_basis b`. Rewrite `h` using `[Module.finrank_fin_fun, Fintype.card_fin]`. Conclude with `h.symm`. Substitute `hnd` using the available equality.

Establish `hb : IsUnit ((Pi.basisFun K (Fin n)).det b)` using `(Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).1 ⟨b.linearIndependent, b.span_eq⟩`. Establish `hb' : IsUnit ((Pi.basisFun K (Fin n)).det (fun q => frobVec p (b q)))`. Rewrite using `[det_frobVec p (⇑b)]`. Conclude with `hb.pow p`. Take `⟨hli, hsp⟩` from `(Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).2 hb'`.

Conclude with `⟨Module.Basis.mk hli hsp.ge, fun q => Module.Basis.mk_apply _ _ _⟩`.
-/
theorem exists_frob_basis {n d : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ q, b' q = frobVec p (b q) := by
  have hnd : n = d := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    exact h.symm
  subst hnd
  have hb : IsUnit ((Pi.basisFun K (Fin n)).det b) :=
    (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).1 ⟨b.linearIndependent, b.span_eq⟩
  have hb' : IsUnit ((Pi.basisFun K (Fin n)).det (fun q => frobVec p (b q))) := by
    rw [det_frobVec p (⇑b)]; exact hb.pow p
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).2 hb'
  exact ⟨Module.Basis.mk hli hsp.ge, fun q => Module.Basis.mk_apply _ _ _⟩

/- English proof (translation)
Use `haveI : ExpChar K p := ExpChar.prime Fact.out`. Establish `key : frobVec p y = ∑ i, (b.repr y i) ^ p • b' i` using `by conv_lhs => rw [← b.sum_repr y]`. Use function extensionality and compare the values at `j`. Simplify using `only [frobVec, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_pow_char, mul_pow]`. Rewrite using `[key, Module.Basis.repr_sum_self]`.
-/
theorem repr_frobVec {n d : ℕ} (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (y : Fin d → K) (q : Fin n) :
    b'.repr (frobVec p y) q = (b.repr y q) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  have key : frobVec p y = ∑ i, (b.repr y i) ^ p • b' i := by
    conv_lhs => rw [← b.sum_repr y]
    funext j
    simp only [frobVec, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_pow_char, mul_pow]
  rw [key, Module.Basis.repr_sum_self]

/- English proof (translation)
Introduce `x`. Express the relevant statement in the definitionally equal form `x ∈ AddSubgroup.closure _ ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hle : AddSubgroup.closure {y | ∃ (a : K) (z : Fin d → K), C.v i a ≤ 1 ∧ z ∈ L i ∧ y = a • frobVec p z} ≤ GlobalTheory.CompanionTheory.Ar.Crv.Inhab.latOf C i b'`.

Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `y ⟨a, z, ha, hz, rfl⟩`. Express the relevant statement in the definitionally equal form `∀ q, C.v i (b'.repr (a • frobVec p z) q) ≤ 1`. Introduce `q`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, repr_frobVec p b b' h z q, map_mul, map_pow]`.

Conclude with `mul_le_one' ha (pow_le_one' ((hb z).1 hz q) p)`. Conclude with `hle hx`. Introduce `hx`. Rewrite using `[← b'.sum_repr x]`. Use `AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ⟨b'.repr x q, b q, hx q, (hb (b q)).2 fun r => ?_, by rw [h]⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isLatOf_frob {n d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (i : C.I)
    (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (hb : IsLatOf C i b (L i)) :
    IsLatOf C i b' (frobLat C p L i) := by
  intro x
  change x ∈ AddSubgroup.closure _ ↔ _
  constructor
  · intro hx
    have hle : AddSubgroup.closure {y | ∃ (a : K) (z : Fin d → K), C.v i a ≤ 1 ∧ z ∈ L i ∧
        y = a • frobVec p z} ≤ GlobalTheory.CompanionTheory.Ar.Crv.Inhab.latOf C i b' := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨a, z, ha, hz, rfl⟩
      change ∀ q, C.v i (b'.repr (a • frobVec p z) q) ≤ 1
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, repr_frobVec p b b' h z q, map_mul, map_pow]
      exact mul_le_one' ha (pow_le_one' ((hb z).1 hz q) p)
    exact hle hx
  · intro hx
    rw [← b'.sum_repr x]
    refine AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure
      ⟨b'.repr x q, b q, hx q, (hb (b q)).2 fun r => ?_, by rw [h]⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

/- English proof (translation)
Take `⟨h1, b₀, hfin⟩` from `hL`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `h1 i`. Take `⟨b', hb'⟩` from `exists_frob_basis p b`. Conclude with `⟨b', isLatOf_frob C p L i b b' hb' hb⟩`.

Take `⟨b', hb'⟩` from `exists_frob_basis p b₀`. Use `⟨b', hfin.subset fun i hi => ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `absurd (isLatOf_frob C p L i b₀ b' hb' h) hi`.
-/
theorem isBun_frobLat {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (hL : IsBun C L) :
    IsBun C (frobLat C p L) := by
  obtain ⟨h1, b₀, hfin⟩ := hL
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h1 i
    obtain ⟨b', hb'⟩ := exists_frob_basis p b
    exact ⟨b', isLatOf_frob C p L i b b' hb' hb⟩
  · obtain ⟨b', hb'⟩ := exists_frob_basis p b₀
    refine ⟨b', hfin.subset fun i hi => ?_⟩
    intro h
    exact absurd (isLatOf_frob C p L i b₀ b' hb' h) hi

/- English proof (translation)
Introduce `K _ C p _ _ d L hL`. Establish `hL'` using `isBun_frobLat C p L hL`. Use `⟨hL', ?_⟩` and prove the remaining obligations. Use `choose b hb using hL.1`. Use `choose b' hb' using fun i => exists_frob_basis p (b i)`.

Establish `e : Fin d ≃ Fin (Module.finrank K (Fin d → K))` using `finCongr (Module.finrank_fin_fun K).symm`. Use `set b₀ := (Pi.basisFun K (Fin d)).reindex e with hb₀`. Establish `hdet : ∀ i, b₀.det (b' i) = (b₀.det (b i)) ^ p`. Introduce `i`. Rewrite using `[hb₀, Module.Basis.det_reindex, Module.Basis.det_reindex]`.

Establish `hc : (⇑(b' i) ∘ ⇑e) = fun q => frobVec p ((⇑(b i) ∘ ⇑e) q)`. Use function extensionality and compare the values at `q`. Conclude with `hb' i (e q)`. Rewrite using `[hc, det_frobVec]`. Take `⟨-, h1⟩` from `GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) L _ b₀ b hL hb`.

Take `⟨-, h2⟩` from `GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) (frobLat C p L) _ b₀ b' hL' (fun i => isLatOf_frob C p L i (b i) (b' i) (hb' i) (hb i))`. Rewrite using `[h1, h2, mul_finsum]`. Use `finsum_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[hdet, map_pow, WithZero.log_pow, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_frobLat : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L →
      IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  intro K _ C p _ _ d L hL
  have hL' := isBun_frobLat C p L hL
  refine ⟨hL', ?_⟩
  choose b hb using hL.1
  choose b' hb' using fun i => exists_frob_basis p (b i)
  have e : Fin d ≃ Fin (Module.finrank K (Fin d → K)) := finCongr (Module.finrank_fin_fun K).symm
  set b₀ := (Pi.basisFun K (Fin d)).reindex e with hb₀
  have hdet : ∀ i, b₀.det (b' i) = (b₀.det (b i)) ^ p := by
    intro i
    rw [hb₀, Module.Basis.det_reindex, Module.Basis.det_reindex]
    have hc : (⇑(b' i) ∘ ⇑e) = fun q => frobVec p ((⇑(b i) ∘ ⇑e) q) := by
      funext q; exact hb' i (e q)
    rw [hc, det_frobVec]
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) L _ b₀ b hL hb
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) (frobLat C p L) _ b₀ b' hL'
    (fun i => isLatOf_frob C p L i (b i) (b' i) (hb' i) (hb i))
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  rw [hdet, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.DegFrob
