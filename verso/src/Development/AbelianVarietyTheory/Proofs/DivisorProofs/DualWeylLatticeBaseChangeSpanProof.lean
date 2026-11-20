import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorLatSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Columns.CoefficientsModP

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.BasicNotions MvPolynomial
open scoped Matrix

namespace GlobalTheory.NabBC

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩`.
-/
theorem mem_localization_of_mem' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L : Submodule R W} {x : W} (h : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩

abbrev vmap {n : ℕ} (f : K₀ →+* K) (x : Fin n → K₀) : Fin n → K := fun a => f (x a)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[vmap]`.
-/
theorem vmap_add {n : ℕ} (f : K₀ →+* K) (x y : Fin n → K₀) : vmap f (x + y) = vmap f x + vmap f y := by
  funext a; simp [vmap]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem vmap_smul {n : ℕ} (f : K₀ →+* K) (r : 𝓞 K₀) (x : Fin n → K₀) :
    vmap f (r • x) = RingOfIntegers.mapRingHom f r • vmap f x := by
  funext a
  change f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)
  rw [map_mul]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero`. Establish `: vmap f (0 : Fin n → K₀) = 0` using `by funext a; simp [vmap]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [vmap_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul r y _ hy => rw [vmap_smul]`. Conclude with `Submodule.smul_mem _ _ hy`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_image_span {n : ℕ} (f : K₀ →+* K) (S : Set (Fin n → K₀)) :
    Submodule.span (𝓞 K) (vmap f '' (Submodule.span (𝓞 K₀) S : Set (Fin n → K₀))) =
      Submodule.span (𝓞 K) (vmap f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : vmap f (0 : Fin n → K₀) = 0 := by funext a; simp [vmap]
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [vmap_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [vmap_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Establish `key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀))))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Take `⟨t, ht, hta⟩` from `h ha`. Conclude with `show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩`.

Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, htx⟩` from `key hsx`. Conclude with `show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩`.
-/
theorem localization_span_image_le {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {A B : Submodule (𝓞 K₀) (Fin n → K₀)} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀)))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
  have key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := h ha
    exact show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from
      ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := key hsx
  exact show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from
    ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩

/- English proof (translation)
Unfold `colLat`. Rewrite using `[span_image_span, ← Set.range_comp]`. Use `congr 1`.
-/
theorem span_vmap_colLat {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    Submodule.span (𝓞 K) (vmap f '' (colLat C : Set (Fin n → K₀))) = colLat (Formalism.UG.bc f C) := by
  unfold colLat
  rw [span_image_span, ← Set.range_comp]
  congr 1

/- English proof (translation)
Unfold `IsBasisAt at hC ⊢`. Rewrite using `[← span_vmap_colLat]`. Establish `h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C)` using `hC ▸ fun x hx => mem_localization_of_mem' _ hx`. Establish `h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L` using `hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx`. Conclude with `le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)`.
-/
theorem isBasisAt_span_vmap {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {L : Submodule (𝓞 K₀) (Fin n → K₀)} {C : GL (Fin n) K₀} (hC : IsBasisAt w₀ L C) :
    IsBasisAt w (Submodule.span (𝓞 K) (vmap f '' (L : Set (Fin n → K₀)))) (Formalism.UG.bc f C) := by
  unfold IsBasisAt at hC ⊢
  rw [← span_vmap_colLat]
  have h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C) := hC ▸ fun x hx => mem_localization_of_mem' _ hx
  have h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L := hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx
  exact le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)

/- English proof (translation)
Unfold `tauLat`. Rewrite using `[span_image_span, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K) (emb : ι → E →+* K₀) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) :
    tauLat (fun τ => f.comp (emb τ)) τ M = Submodule.span (𝓞 K) (vmap f '' (tauLat emb τ M : Set (Fin n → K₀))) := by
  unfold tauLat
  rw [span_image_span, Set.image_image]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]`. Both sides reduce to the same expression.
-/
theorem invTr_bc {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    inside₂ K n (Formalism.UG.bc f C) = Formalism.UG.bc f (inside₂ K₀ n C) := by
  apply Units.ext
  change (((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]
  rfl

/- English proof (translation)
Rewrite using `[← invTr_bc]`. Use `GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_` and prove the remaining obligations. Rewrite using `[tauLat_comp]`. Conclude with `isBasisAt_span_vmap f w₀ w hw hC`.
-/
theorem isBasisAt_dualFr_tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (τ : ι) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M)
    (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    (C : GL (Fin n) K₀) (hC : IsBasisAt w₀ (tauLat emb τ M) C) :
    IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (inside₂ K₀ n C)) := by
  rw [← invTr_bc]
  refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_
  rw [tauLat_comp]
  exact isBasisAt_span_vmap f w₀ w hw hC

/- English proof (translation)
Establish `h1` using `(GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1`. Establish `h2` using `(GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1`. Rewrite using `[h1, ← h2]`. Introduce `x hx`. Conclude with `Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩`.
-/
theorem nabStd_le_span_map {ι : Type} [Fintype ι] {n : ℕ} (f : K₀ →+* K) (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]`. Express the relevant statement in the definitionally equal form `((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem map_smul_int {σ : Type} (f : K₀ →+* K) (t : 𝓞 K₀) (P : MvPolynomial σ K₀) :
    RingOfIntegers.mapRingHom f t • MvPolynomial.map f P = MvPolynomial.map f (t • P) := by
  ext m
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change ((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)
  rw [map_mul]
  rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀), ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by`. Use `⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩` and prove the remaining obligations. Establish `h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f)`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem _`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))`. Establish `hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal` using `fun t ht h => ht ((hw₀ t).2 h)`. Take `⟨hLoc, -, -⟩` from `GlobalTheory.TransLoc.nabDelLoc_free_leVV`. Establish `hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M)` using `fun τ => tauLatLattice E K₀ ι n emb τ M hM`.

Use `choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀`. Set `B₀ : ι → GL (Fin n) K₀` to `fun τ => inside₂ K₀ n (C τ)`. Establish `hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ)` using `fun τ => GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)`. Establish `hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ))` using `fun τ => isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)`. Establish `L1` using `(hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1`.

Establish `L0` using `(hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1`. Use `set N' := Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'`. Establish `key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))), actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'`. Introduce `H hH`. Use `(Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'`. Rewrite using `[← GlobalTheory.ValCmp.use₂]`. Establish `hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M))`. Rewrite using `[L0]`.

Conclude with `Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)`. Take `⟨t, ht, htg⟩` from `hg'`. Use `⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩` and prove the remaining obligations. Establish `e` using `map_smul_int f t (actP lam B₀ g)`. Use `(congrArg (· ∈ N') e).mpr ?_` and prove the remaining obligations.

Conclude with `Submodule.subset_span ⟨_, htg, rfl⟩`. Establish `hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M))` using `mem_localization_of_mem' _ hF`. Rewrite `hF'` using `[L1]`. Take `⟨G, ⟨s, hs, hsG⟩, rfl⟩` from `hF'`. Take `⟨t, ht, htG⟩` from `key _ (nabStd_le_span_map f lam hsG)`.

Use `⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩` and prove the remaining obligations. Use `htG using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_smul]`. Use `congr 1`. Conclude with `(((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm`.
-/
theorem mem_localization_span_map {E ι : Type} [Field E] [NumberField E] [Fintype ι] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M)
    (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n}
    (hF : F ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))) := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  set N' := Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'
  have key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))),
      actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' := by
    intro H hH
    refine (Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap
      ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH
    rintro _ ⟨g, hg, rfl⟩
    show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'
    rw [← GlobalTheory.ValCmp.use₂]
    have hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) := by
      rw [L0]
      exact Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)
    obtain ⟨t, ht, htg⟩ := hg'
    refine ⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩
    have e := map_smul_int f t (actP lam B₀ g)
    refine (congrArg (· ∈ N') e).mpr ?_
    exact Submodule.subset_span ⟨_, htg, rfl⟩
  have hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :=
    mem_localization_of_mem' _ hF
  rw [L1] at hF'
  obtain ⟨G, ⟨s, hs, hsG⟩, rfl⟩ := hF'
  obtain ⟨t, ht, htG⟩ := key _ (nabStd_le_span_map f lam hsG)
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  convert htG using 1
  rw [mul_smul]
  congr 1
  exact (((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm

/- English proof (translation)
Introduce `E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF`. Take `⟨-, -, hV⟩` from `GlobalTheory.TransLoc.nabDelLoc_free_leVV`. Establish `hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))` using `GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF`. Establish `hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) '' {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} = MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))`. Use extensionality with `P`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨x, hx, hxy⟩, rfl⟩`. Conclude with `⟨x.1, hx, hxy.symm⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Establish `hxV : x ∈ VV K₀ lam` using `hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx`.

Conclude with `⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩`. Rewrite `hP` using `[← hS, ← Submodule.map_span]`. Take `⟨y, hy, hyF⟩` from `hP`. Establish `e : y = F` using `Subtype.ext hyF`. Rewrite using `[← e]` and apply the resulting hypothesis.
-/
theorem nabBaseChange : GlobalTheory.BaseCmp.NabBaseChange := by
  intro E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF
  obtain ⟨-, -, hV⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) :=
    GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF
  have hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) ''
      {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} =
      MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)) := by
    ext P
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      exact ⟨x.1, hx, hxy.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ VV K₀ lam := hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx
      exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩
  rw [← hS, ← Submodule.map_span] at hP
  obtain ⟨y, hy, hyF⟩ := hP
  have e : y = F := Subtype.ext hyF
  rwa [← e]

end GlobalTheory.NabBC
