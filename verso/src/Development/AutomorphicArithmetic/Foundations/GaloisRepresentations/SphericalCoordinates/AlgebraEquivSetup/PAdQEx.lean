import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare in
/- English proof (translation)
Establish `mem : ∀ {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] (v : HeightOneSpectrum R) (n : ℕ), (n : R) ∈ v.asIdeal ↔ natGenerator v ∣ n`. Introduce `R _ _ _ v n`. Rewrite using `[natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv R) n, Ideal.apply_mem_of_equiv_iff]`. Establish `key : primesEquiv (primeCorr w) = primesEquiv w`. Express the relevant statement in the definitionally equal form `primesEquiv (primesEquiv.symm (primesEquiv w)) = _`.

Conclude with `Equiv.apply_symm_apply _ _`. Establish `hg : natGenerator (primeCorr w) = natGenerator w` using `congrArg Subtype.val key`. Rewrite using `[mem, hg, ← mem (R := ℤ)]`. Use `not_congr ⟨fun h ↦ h ▸ Ideal.mem_span_singleton_self _, fun h ↦ ?_⟩` and prove the remaining obligations. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible`.

Conclude with `(hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm`.
-/
private theorem away_iff (p : ℕ) [hp : Fact p.Prime] (w : HeightOneSpectrum ℤ) :
    w.asIdeal ≠ Ideal.span {(p : ℤ)} ↔ (p : 𝓞 ℚ) ∉ (primeCorr w).asIdeal := by
  have mem : ∀ {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
      (v : HeightOneSpectrum R) (n : ℕ), (n : R) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
    intro R _ _ _ v n
    rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv R) n,
      Ideal.apply_mem_of_equiv_iff]
  have key : primesEquiv (primeCorr w) = primesEquiv w := by
    change primesEquiv (primesEquiv.symm (primesEquiv w)) = _
    exact Equiv.apply_symm_apply _ _
  have hg : natGenerator (primeCorr w) = natGenerator w := congrArg Subtype.val key
  rw [mem, hg, ← mem (R := ℤ)]
  refine not_congr ⟨fun h ↦ h ▸ Ideal.mem_span_singleton_self _, fun h ↦ ?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact (hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨e.toRingEquiv, fun _ ↦ rfl⟩`.
-/
private theorem ringEquiv_of_algEquiv {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    {_ : Algebra K A} {_ : Algebra K B} (e : A ≃ₐ[K] B) : ∃ f : A ≃+* B, ∀ x, f x = e x := ⟨e.toRingEquiv, fun _ ↦ rfl⟩

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
Take `⟨e, he⟩` from `exists_local w`. Take `⟨f, hf⟩` from `ringEquiv_of_algEquiv e`. Conclude with `⟨f, fun x ↦ by rw [hf]; exact he x⟩`.
-/
private theorem exists_local_ring (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  obtain ⟨e, he⟩ := exists_local w
  obtain ⟨f, hf⟩ := ringEquiv_of_algEquiv e
  exact ⟨f, fun x ↦ by rw [hf]; exact he x⟩

open GlobalTheory.NormLevelCompare in
private noncomputable def eL (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ :=
  Classical.choose (exists_local_ring w)

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_local_ring w) x`.
-/
private theorem eL_mem (w : HeightOneSpectrum ℤ) (x : (primeCorr w).adicCompletion ℚ) :
    eL w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := Classical.choose_spec (exists_local_ring w) x

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
The claim follows from `fun x hx ↦ (eL_mem w x).2 hx`.
-/
private theorem eL_mapsTo (w : HeightOneSpectrum ℤ) :
    Set.MapsTo (eL w).toRingHom ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) := fun x hx ↦ (eL_mem w x).2 hx

/- English proof (translation)
The claim follows from `RestrictedProduct.ext _ _ h`.
-/
private theorem finiteAdeleRingAway_ext {p : ℕ} {x y : AfP p} (h : ∀ v, AfP.eval v x = AfP.eval v y) : x = y := RestrictedProduct.ext _ _ h

open GlobalTheory.NormLevelCompare in
private noncomputable def rho (p : ℕ) : AfQ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun u : HeightOneSpectrum (𝓞 ℚ) ↦ u.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ)
    (B₁ := fun u ↦ u.adicCompletionIntegers ℚ) (B₂ := fun v ↦ v.1.adicCompletionIntegers ℚ)
    (fun v ↦ primeCorr v.1) (primeCorr.injective.comp Subtype.val_injective).tendsto_cofinite
    (fun v ↦ (eL v.1).toRingHom) (hφ := .of_forall fun v ↦ eL_mapsTo v.1)

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem eval_rho {p : ℕ} (a : AfQ) (v : AwayP p) :
    AfP.eval v (rho p a) = eL v.1 (a (primeCorr v.1)) := rfl

section
open GlobalTheory.NormLevelCompare
open scoped Classical in
private noncomputable def gL {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ :=
  if h : w.asIdeal ≠ Ideal.span {(p : ℤ)} then (eL w).symm (AfP.eval (⟨w, h⟩ : AwayP p) b) else 0

/- English proof (translation)
Unfold `gL`. Rewrite using `[dif_pos v.2]`. Both sides reduce to the same expression.
-/
private theorem gL_pos {p : ℕ} (b : AfP p) (v : AwayP p) : gL b v.1 = (eL v.1).symm (AfP.eval v b) := by
  unfold gL
  rw [dif_pos v.2]
  rfl

/- English proof (translation)
Unfold `gL`. Rewrite using `[dif_neg h]`.
-/
private theorem gL_neg {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ)
    (h : ¬ w.asIdeal ≠ Ideal.span {(p : ℤ)}) : gL b w = 0 := by
  unfold gL
  rw [dif_neg h]

/- English proof (translation)
The claim follows from `b.2`.
-/
private theorem afP_ev {p : ℕ} (b : AfP p) :
    ∀ᶠ v : AwayP p in Filter.cofinite, AfP.eval v b ∈ v.1.adicCompletionIntegers ℚ := b.2

/- English proof (translation)
Establish `hb` using `afP_ev b`. Rewrite `hb`, the goal using `[Filter.eventually_cofinite]`. Use `(hb.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce `w hw`. Distinguish the cases in `h : w.asIdeal ≠ Ideal.span {(p : ℤ)}`.

Use `⟨⟨w, h⟩, ?_, rfl⟩` and prove the remaining obligations. Introduce `hv`. Apply `hw` to reduce the goal to its premises. Rewrite using `[show gL b w = _ from gL_pos b ⟨w, h⟩]`. Conclude with `(eL_mem w _).1 (by simpa using hv)`.

Conclude with `absurd (by rw [gL_neg b w h]; exact zero_mem _) hw`.
-/
private theorem gL_ev {p : ℕ} (b : AfP p) : ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite,
    gL b w ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have hb := afP_ev b
  rw [Filter.eventually_cofinite] at hb ⊢
  refine (hb.image Subtype.val).subset ?_
  intro w hw
  by_cases h : w.asIdeal ≠ Ideal.span {(p : ℤ)}
  · refine ⟨⟨w, h⟩, ?_, rfl⟩
    intro hv
    apply hw
    rw [show gL b w = _ from gL_pos b ⟨w, h⟩]
    exact (eL_mem w _).1 (by simpa using hv)
  · exact absurd (by rw [gL_neg b w h]; exact zero_mem _) hw

/- English proof (translation)
Assemble the required witnesses or components as `⟨Equiv.piCongrLeft P σ g, fun a ↦ Equiv.piCongrLeft_apply_apply P σ g a⟩`.
-/
private theorem exists_pi_extend {α β : Type*} (P : β → Type*) (σ : α ≃ β) (g : ∀ a, P (σ a)) :
    ∃ f : ∀ b, P b, ∀ a, f (σ a) = g a := ⟨Equiv.piCongrLeft P σ g, fun a ↦ Equiv.piCongrLeft_apply_apply P σ g a⟩

private noncomputable def fL {p : ℕ} (b : AfP p) : ∀ u : HeightOneSpectrum (𝓞 ℚ), u.adicCompletion ℚ :=
  Classical.choose (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b))

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b)) w`.
-/
private theorem fL_corr {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) : fL b (primeCorr w) = gL b w := Classical.choose_spec
  (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b)) w

/- English proof (translation)
Establish `hg` using `gL_ev b`. Rewrite `hg`, the goal using `[Filter.eventually_cofinite]`. Use `(hg.image primeCorr).subset ?_` and prove the remaining obligations. Introduce `u hu`. Take `⟨w, rfl⟩` from `primeCorr.surjective u`.

Use `⟨w, ?_, rfl⟩` and prove the remaining obligations. Introduce `hw`. Apply `hu` to reduce the goal to its premises. Rewrite using `[fL_corr]`. Conclude with `hw`.
-/
private theorem fL_ev {p : ℕ} (b : AfP p) : ∀ᶠ u : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
    fL b u ∈ u.adicCompletionIntegers ℚ := by
  have hg := gL_ev b
  rw [Filter.eventually_cofinite] at hg ⊢
  refine (hg.image primeCorr).subset ?_
  intro u hu
  obtain ⟨w, rfl⟩ := primeCorr.surjective u
  refine ⟨w, ?_, rfl⟩
  intro hw
  apply hu
  rw [fL_corr]
  exact hw

private noncomputable def liftA {p : ℕ} (b : AfP p) : AfQ := ⟨fL b, fL_ev b⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem liftA_apply {p : ℕ} (b : AfP p) (u : HeightOneSpectrum (𝓞 ℚ)) : liftA b u = fL b u := rfl

/- English proof (translation)
Introduce `b`. Use `⟨liftA b, finiteAdeleRingAway_ext fun v ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[eval_rho, liftA_apply, fL_corr, gL_pos, RingEquiv.apply_symm_apply]`.
-/
private theorem rho_surj (p : ℕ) : Function.Surjective (rho p) := by
  intro b
  refine ⟨liftA b, finiteAdeleRingAway_ext fun v ↦ ?_⟩
  rw [eval_rho, liftA_apply, fL_corr, gL_pos, RingEquiv.apply_symm_apply]
end

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Take `⟨w, rfl⟩` from `primeCorr.surjective v`. Establish `h2 : eL w (a (primeCorr w)) = 0` using `(congrArg (AfP.eval (⟨w, (away_iff p w).2 hv⟩ : AwayP p)) h).trans (map_zero _)`. Conclude with `(map_eq_zero_iff _ (eL w).injective).1 h2`.

Introduce `h`. Use `finiteAdeleRingAway_ext fun v ↦ ?_` and prove the remaining obligations. Rewrite using `[eval_rho, map_zero, h _ ((away_iff p v.1).1 v.2), map_zero]`.
-/
private theorem rho_ker (p : ℕ) [Fact p.Prime] (a : AfQ) :
    rho p a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) = 0 :=
      (congrArg (AfP.eval (⟨w, (away_iff p w).2 hv⟩ : AwayP p)) h).trans (map_zero _)
    exact (map_eq_zero_iff _ (eL w).injective).1 h2
  · intro h
    refine finiteAdeleRingAway_ext fun v ↦ ?_
    rw [eval_rho, map_zero, h _ ((away_iff p v.1).1 v.2), map_zero]

open GlobalTheory.NormLevelCompare in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Take `⟨w, rfl⟩` from `primeCorr.surjective v`. Establish `h2 : eL w (a (primeCorr w)) ∈ w.adicCompletionIntegers ℚ` using `h ⟨w, (away_iff p w).2 hv⟩`. Rewrite `h2` using `[eL_mem]`.

Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2`. Introduce `h v show AfP.eval v (rho p a) ∈ _`. Rewrite using `[eval_rho, eL_mem]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h _ ((away_iff p v.1).1 v.2))`.
-/
private theorem rho_int (p : ℕ) [Fact p.Prime] (a : AfQ) :
    IsIntAf (rho p a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) ∈ w.adicCompletionIntegers ℚ := h ⟨w, (away_iff p w).2 hv⟩
    rw [eL_mem] at h2
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
  · intro h v
    show AfP.eval v (rho p a) ∈ _
    rw [eval_rho, eL_mem]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h _ ((away_iff p v.1).1 v.2))

/- English proof (translation)
The claim follows from `fun p _ ↦ ⟨⟨rho p, rho_surj p, rho_ker p, rho_int p⟩⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pAdQEx :
    AdQEx := fun p _ ↦ ⟨⟨rho p, rho_surj p, rho_ker p, rho_int p⟩⟩
