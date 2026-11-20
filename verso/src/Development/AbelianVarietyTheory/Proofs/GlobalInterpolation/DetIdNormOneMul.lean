import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.RelDetIdeal

open GlobalTheory.CharValCompare GlobalTheory.Survey.StandardDeterminantUnits

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def relDet (L L' : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

omit [StarRing E] in
/- English proof (translation)
The claim follows from `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h)`.
-/
theorem val_pos {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : a ≠ 0) : 0 < P.valuation E a :=
  zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h)

omit [StarRing E] in
/- English proof (translation)
Use `gen_of (mul_ne_zero ha.1 hb.1) ?_ fun x hx => ?_` and prove the remaining obligations. Take `⟨s, hs, h1⟩` from `(ha.2 a).2 le_rfl`. Take `⟨t, ht, h2⟩` from `(hb.2 b).2 le_rfl`. Use `⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_mul_smul_comm]`.

Conclude with `Submodule.mul_mem_mul h1 h2`. Use `Submodule.mul_induction_on hx (fun m hm k hk => ?_) (fun x y hx hy => Valuation.map_add_le _ hx hy)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Conclude with `mul_le_mul' ((ha.2 m).1 (ThetaMove.mem_localization_of_mem P hm)) ((hb.2 k).1 (ThetaMove.mem_localization_of_mem P hk))`.
-/
theorem gen_mul {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {a b : E} (ha : Gen P I a) (hb : Gen P J b) :
    Gen P (I * J) (a * b) := by
  refine gen_of (mul_ne_zero ha.1 hb.1) ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    obtain ⟨t, ht, h2⟩ := (hb.2 b).2 le_rfl
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    rw [← smul_mul_smul_comm]
    exact Submodule.mul_mem_mul h1 h2
  · refine Submodule.mul_induction_on hx (fun m hm k hk => ?_) (fun x y hx hy => Valuation.map_add_le _ hx hy)
    rw [map_mul, map_mul]
    exact mul_le_mul' ((ha.2 m).1 (ThetaMove.mem_localization_of_mem P hm)) ((hb.2 k).1 (ThetaMove.mem_localization_of_mem P hk))

omit [StarRing E] in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Conclude with `ThetaMove.mem_of_locP fun P => ((hb P).2 x).2 (h P ▸ ((ha P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))`. Introduce `x hx`. Conclude with `ThetaMove.mem_of_locP fun P => ((ha P).2 x).2 ((h P).symm ▸ ((hb P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))`.
-/
theorem eq_of_gen {I J : Submodule (𝓞 E) E} (a b : HeightOneSpectrum (𝓞 E) → E) (ha : ∀ P, Gen P I (a P)) (hb : ∀ P, Gen P J (b P))
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (a P) = P.valuation E (b P)) : I = J := by
  apply le_antisymm
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((hb P).2 x).2 (h P ▸ ((ha P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((ha P).2 x).2 ((h P).symm ▸ ((hb P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))

omit [StarRing E] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, fun x => by rw [mem_localization_one, intAt_iff, map_one]⟩`.
-/
theorem gen_one (P : HeightOneSpectrum (𝓞 E)) : Gen P (1 : Submodule (𝓞 E) E) 1 :=
  ⟨one_ne_zero, fun x => by rw [mem_localization_one, intAt_iff, map_one]⟩

/- English proof (translation)
Establish `h0 : star a ≠ 0` using `star_ne_zero.2 ha.1`. Use `gen_of h0 ?_ fun x hx => ?_` and prove the remaining obligations. Take `⟨s, hs, h1⟩` from `(ha.2 a).2 le_rfl`. Use `⟨cO E s, hs, ?_⟩` and prove the remaining obligations. Use `show star (cO E s • star a) ∈ I`.

Rewrite using `[Algebra.smul_def, algebraMap_cO, star_mul', star_star, star_star, ← Algebra.smul_def]` and apply the resulting hypothesis. Establish `h2` using `(ha.2 (star x)).1 (ThetaMove.mem_localization_of_mem _ hx)`. Establish `h3 : IntAt (conjPrime₂ P) (star x / a)`. Rewrite using `[intAt_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ h2 zero_le`.

Establish `h4` using `intAt_iff.1 (intAt_star h3)`. Rewrite `h4` using `[conjP_conjP, star_div₀, star_star, map_div₀, div_le_one₀ (val_pos h0)]`. Then use the resulting hypothesis.
-/
theorem gen_bar {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a : E} (ha : Gen (conjPrime₂ P) I a) :
    Gen P (barI I) (star a) := by
  have h0 : star a ≠ 0 := star_ne_zero.2 ha.1
  refine gen_of h0 ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    refine ⟨cO E s, hs, ?_⟩
    show star (cO E s • star a) ∈ I
    rwa [Algebra.smul_def, algebraMap_cO, star_mul', star_star, star_star, ← Algebra.smul_def]
  · have h2 := (ha.2 (star x)).1 (ThetaMove.mem_localization_of_mem _ hx)
    have h3 : IntAt (conjPrime₂ P) (star x / a) := by
      rw [intAt_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    have h4 := intAt_iff.1 (intAt_star h3)
    rwa [conjP_conjP, star_div₀, star_star, map_div₀, div_le_one₀ (val_pos h0)] at h4

/- English proof (translation)
Use `gen_of (div_ne_zero (dt_ne _) (dt_ne _)) ?_ ?_` and prove the remaining obligations. Set `g : Sp E n →ₗ[E] Sp E n` to `(f' : Sp E n →ₗ[E] Sp E n) ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n)`. Establish `hg : ∀ v ∈ L, g v ∈ localization₂ P.asIdeal L'` using `fun v hv => (hf' _).2 ((hf _).1 (by simpa using ThetaMove.mem_localization_of_mem P hv))`. Take `⟨S, rfl⟩` from `hL`. Establish `: ∀ i : S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • g i ∈ L'` using `fun i => hg i (Submodule.subset_span i.2)`.

Use `choose s hs hs' using this`. Establish `hp : ∏ i, s i ∉ P.asIdeal` using `fun hm => by`. Take `⟨y, _, h⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm`. Conclude with `hs y h`. Use `⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' g, fun v hv => ?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`. Rewrite using `[← Finset.prod_erase_mul _ s (Finset.mem_univ ⟨y, hy⟩), mul_smul]`. Conclude with `L'.smul_mem _ (hs' ⟨y, hy⟩)`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, smul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]`.

Conclude with `L'.smul_mem _ ha`. Establish `e : LinearMap.det g = dt f' / dt f`. Rewrite using `[eq_div_iff (dt_ne _), LinearMap.det_comp, dt_eq, dt_eq, mul_assoc, LinearEquiv.det_symm_mul_det, mul_one]`. Rewrite using `[Matrix.det_smul, LinearMap.det_toMatrix', e, Algebra.smul_def, map_pow, Fintype.card_fin]`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨A, hA, rfl⟩` from `hy`. Establish `h1` using `val_det_le_one (P := P) ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) fun x hx => by`. Rewrite using `[← hf']`.

Take `⟨s, hs, hx⟩` from `(hf x).2 hx`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `hA _ hx` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E s (f x), Matrix.mulVec_smul, algebraMap_smul]`. Simplify using `using this`.

Establish `h2 : A.det = dt f' / dt f * LinearMap.det ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n))`. Establish `h3` using `LinearEquiv.det_mul_det_symm f'`. Establish `h4` using `dt_ne f`. Rewrite using `[LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', ← dt_eq f]`. Rewrite `h3` using `[← dt_eq f']`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-A.det) * h3`. Rewrite using `[h2, map_mul]`. Conclude with `mul_le_of_le_one_right' h1`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha`.
-/
theorem gen_relDet {P : HeightOneSpectrum (𝓞 E)} {L L' : Submodule (𝓞 E) (Sp E n)} (hL : L.FG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P L f) (hf' : IsFr P L' f') : Gen P (relDet L L') (dt f' / dt f) := by
  classical
  refine gen_of (div_ne_zero (dt_ne _) (dt_ne _)) ?_ ?_
  · let g : Sp E n →ₗ[E] Sp E n := (f' : Sp E n →ₗ[E] Sp E n) ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n)
    have hg : ∀ v ∈ L, g v ∈ localization₂ P.asIdeal L' := fun v hv =>
      (hf' _).2 ((hf _).1 (by simpa using ThetaMove.mem_localization_of_mem P hv))
    obtain ⟨S, rfl⟩ := hL
    have : ∀ i : S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • g i ∈ L' := fun i => hg i (Submodule.subset_span i.2)
    choose s hs hs' using this
    have hp : ∏ i, s i ∉ P.asIdeal := fun hm => by
      obtain ⟨y, _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs y h
    refine ⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span
      ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' g, fun v hv => ?_, ?_⟩⟩
    · rw [Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]
      induction hv using Submodule.span_induction with
      | mem y hy =>
        rw [← Finset.prod_erase_mul _ s (Finset.mem_univ ⟨y, hy⟩), mul_smul]
        exact L'.smul_mem _ (hs' ⟨y, hy⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, smul_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]
        exact L'.smul_mem _ ha
    · have e : LinearMap.det g = dt f' / dt f := by
        rw [eq_div_iff (dt_ne _), LinearMap.det_comp, dt_eq, dt_eq, mul_assoc, LinearEquiv.det_symm_mul_det, mul_one]
      rw [Matrix.det_smul, LinearMap.det_toMatrix', e, Algebra.smul_def, map_pow, Fintype.card_fin]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, hA, rfl⟩ := hy
      have h1 := val_det_le_one (P := P)
        ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) fun x hx => by
        rw [← hf']
        obtain ⟨s, hs, hx⟩ := (hf x).2 hx
        refine ⟨s, hs, ?_⟩
        have := hA _ hx
        rw [← algebraMap_smul E s (f x), Matrix.mulVec_smul, algebraMap_smul] at this
        simpa using this
      have h2 : A.det = dt f' / dt f *
          LinearMap.det ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) := by
        have h3 := LinearEquiv.det_mul_det_symm f'
        have h4 := dt_ne f
        rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', ← dt_eq f]
        rw [← dt_eq f'] at h3
        field_simp
        linear_combination (-A.det) * h3
      rw [h2, map_mul]
      exact mul_le_of_le_one_right' h1
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha

/- English proof (translation)
Use `choose f hf using fun P => exists_isFr P hL`. Use `choose f' hf' using fun P => exists_isFr P hL'`. Use `choose f'' hf'' using fun P => exists_isFr P hL''`. Use `eq_of_gen _ _ (fun P => gen_relDet hL.fg (hf P) (hf'' P)) (fun P => gen_mul (gen_relDet hL.fg (hf P) (hf' P)) (gen_relDet hL'.fg (hf' P) (hf'' P))) fun P => ?_` and prove the remaining obligations. Use `congr 1`.

Use `dt_ne (f P)` as an intermediate fact. Use `dt_ne (f' P)` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem relDet_mul {L L' L'' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (hL'' : Submodule.IsLattice E L'') : relDet L L'' = relDet L L' * relDet L' L'' := by
  choose f hf using fun P => exists_isFr P hL
  choose f' hf' using fun P => exists_isFr P hL'
  choose f'' hf'' using fun P => exists_isFr P hL''
  refine eq_of_gen _ _ (fun P => gen_relDet hL.fg (hf P) (hf'' P))
    (fun P => gen_mul (gen_relDet hL.fg (hf P) (hf' P)) (gen_relDet hL'.fg (hf' P) (hf'' P))) fun P => ?_
  congr 1
  have := dt_ne (f P)
  have := dt_ne (f' P)
  field_simp

/- English proof (translation)
Use `⟨barI (relDet L L'), fun _ => Iff.rfl, ?_⟩` and prove the remaining obligations. Use `choose f hf using fun P => exists_isFr P hL.1`. Use `choose f' hf' using fun P => exists_isFr P hL'.1`. Establish `hg` using `fun P => gen_relDet hL.1.fg (hf P) (hf' P)`. Use `eq_of_gen _ _ (fun P => gen_mul (hg P) (gen_bar (hg (conjPrime₂ P)))) gen_one fun P => ?_` and prove the remaining obligations.

Establish `h1` using `val_dual hL (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)`. Establish `h2` using `val_dual hL' (hf' (conjPrime₂ P)) (f' := f' P) (by rw [conjP_conjP]; exact hf' P)`. Rewrite `h1`, `h2` using `[conjP_conjP]`. Rewrite using `[star_div₀, div_mul_div_comm, map_div₀, mul_comm (dt _), mul_comm (dt _), h1, h2, map_one, div_one]`.
-/
theorem normOne_relDet {L L' : Submodule (𝓞 E) (Sp E n)} (hL : IsSdLat L) (hL' : IsSdLat L') : NormOne (relDet L L') := by
  refine ⟨barI (relDet L L'), fun _ => Iff.rfl, ?_⟩
  choose f hf using fun P => exists_isFr P hL.1
  choose f' hf' using fun P => exists_isFr P hL'.1
  have hg := fun P => gen_relDet hL.1.fg (hf P) (hf' P)
  refine eq_of_gen _ _ (fun P => gen_mul (hg P) (gen_bar (hg (conjPrime₂ P)))) gen_one fun P => ?_
  have h1 := val_dual hL (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
  have h2 := val_dual hL' (hf' (conjPrime₂ P)) (f' := f' P) (by rw [conjP_conjP]; exact hf' P)
  rw [conjP_conjP] at h1 h2
  rw [star_div₀, div_mul_div_comm, map_div₀, mul_comm (dt _), mul_comm (dt _), h1, h2, map_one, div_one]

/- English proof (translation)
Use `⟨⟨h.1, h.2.1⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[mem_dual, h.2.2]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_one]`.

Both sides reduce to the same expression.
-/
theorem isSdLat_of {L : Submodule (𝓞 E) (Sp E n)} (h : IsSDLat E n L) : IsSdLat L := by
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  ext x
  rw [mem_dual, h.2.2]
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  rfl

end General

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `hs : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Establish `h1` using `isSdLat_of hL`. Establish `h2` using `isSdLat_of hL'`. Establish `h3` using `isSdLat_of hL''`.

Use `⟨?_, relDet_mul h1.1 h2.1 h3.1⟩` and prove the remaining obligations. Take `⟨J, hJ, e⟩` from `normOne_relDet h1 h2`. Conclude with `⟨J, fun x => by rw [hJ, hs]; rfl, e⟩`.
-/
theorem detId_normOne_mul (D : D7) (n : ℕ) (L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL'' : StandardLatticesGL3.SD D L'') :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D L L') ∧ TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L'' := by
  letI := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 := isSdLat_of hL
  have h2 := isSdLat_of hL'
  have h3 := isSdLat_of hL''
  refine ⟨?_, relDet_mul h1.1 h2.1 h3.1⟩
  obtain ⟨J, hJ, e⟩ := normOne_relDet h1 h2
  exact ⟨J, fun x => by rw [hJ, hs]; rfl, e⟩

end GlobalTheory.RelDetIdeal
