import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeStable

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne :=`. Use the proof step `{ hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Use `haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`. Conclude with `secondCountable_of_proper`.
-/
theorem secondCountable_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Introduce `h0`. Conclude with `(irreducible_uniformizer F).ne_zero (Subtype.ext h0)`.
-/
theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := by
  intro h0
  exact (irreducible_uniformizer F).ne_zero (Subtype.ext h0)

variable (F) in

def scal (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_smul]
  inv_val := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_smul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)) *ᵥ x = _`. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec]`.
-/
theorem scal_mulVec (m M : ℕ) (x : Fin m → F) :
    ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x = ((uniformizer F : F)⁻¹ ^ M) • x := by
  change (((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)) *ᵥ x = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Establish `h` using `unif_ne_zero (F := F)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ i`. Establish `hxi` using `hx i`.

Rewrite `hxi` using `[pow_zero, one_mul]`. Simplify using `only [scal_mulVec m M x, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]` and apply the resulting hypothesis. Introduce `hy`. Use `⟨fun i => (uniformizer F : F) ^ M * y i, fun i => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, one_mul]`. Conclude with `hy i`. Use function extensionality and compare the values at `i`. Simplify using `only [scal_mulVec m M _, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]`.
-/
theorem image_scal (m M : ℕ) :
    (fun x => ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 = lat F m M := by
  have h := unif_ne_zero (F := F)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hxi := hx i
    rw [pow_zero, one_mul] at hxi
    simp only [scal_mulVec m M x, Pi.smul_apply, smul_eq_mul]
    rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]
  · intro hy
    refine ⟨fun i => (uniformizer F : F) ^ M * y i, fun i => ?_, ?_⟩
    · rw [pow_zero, one_mul]; exact hy i
    · funext i
      simp only [scal_mulVec m M _, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]

/- English proof (translation)
Introduce `i j`. Use `⟨(uniformizer F : F) ^ (M - c) * (1 : Matrix (Fin m) (Fin m) F) i j, ?_, ?_⟩` and prove the remaining obligations. Use `mul_mem (pow_mem (uniformizer F).2 _) ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Rewrite using `[hij, Matrix.one_apply_eq]`.

Conclude with `one_mem _`. Rewrite using `[Matrix.one_apply_ne hij]`. Conclude with `zero_mem _`. Express the relevant statement in the definitionally equal form `(((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)) i j = _`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hM]`.
-/
theorem div_scal_inv {m c M : ℕ} (hM : c ≤ M) :
    Div c (((scal F m M)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  intro i j
  refine ⟨(uniformizer F : F) ^ (M - c) * (1 : Matrix (Fin m) (Fin m) F) i j, ?_, ?_⟩
  · refine mul_mem (pow_mem (uniformizer F).2 _) ?_
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · change (((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)) i j = _
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hM]

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
  (ψ : AddChar F ℂ) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) F) V) (k : ℕ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def avg (M : ℕ) (u' u : V) : ℂ :=
  ∫ x in lat F (k + 1) M, ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)

/- English proof (translation)
Use `haveI := secondCountable_field F`. Use `choose m hm using hst`. Establish `hint : ∀ M u' u, IntegrableOn (fun x : Fin (k + 1) → F => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)) (lat F (k + 1) M) (Measure.pi fun _ => μ)`. Introduce `M u' u`. Use `ContinuousOn.integrableOn_compact (hlat M) (Continuous.continuousOn ?_)` and prove the remaining obligations.

Conclude with `(hψ.comp (continuous_apply _).neg).mul (hcont u u')`. Set `f : V → V → ℂ` to `fun u' u => avg μ ψ ρ k B (m u u') u' u`. Establish `hf : ∀ u' u M, m u u' ≤ M → f u' u = avg μ ψ ρ k B M u' u` using `fun u' u M h => (hm u u' M h).symm`. Use `⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) f ?_ ?_ ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `a b w`.

Set `M` to `max (m w (a + b)) (max (m w a) (m w b))`. Rewrite using `[hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)), hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]`. Simplify using `only [avg]`. Rewrite using `[← integral_add (hint M a w) (hint M b w)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `[mul_add]`. Introduce `c a w`. Set `M` to `max (m w (c • a)) (m w a)`. Rewrite using `[hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]`.

Simplify using `only [avg]`. Rewrite using `[smul_eq_mul, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a v w`. Set `M` to `max (m (v + w) a) (max (m v a) (m w a))`. Rewrite using `[hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)), hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]`. Simplify using `only [avg]`.

Rewrite using `[← integral_add (hint M a v) (hint M a w)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[mul_add]`. Introduce `c a v`.

Set `M` to `max (m (c • v) a) (m v a)`. Rewrite using `[hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]`. Simplify using `only [avg]`. Rewrite using `[smul_eq_mul, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u u'`. Conclude with `⟨m u u', fun M hM => hf u' u M hM⟩`.
-/
theorem exists_char (hψ : Continuous ψ) (hlat : ∀ M, IsCompact (lat F (k + 1) M))
    (hcont : ∀ u u', Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)))
    (hst : ∀ u u', ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → avg μ ψ ρ k B M u' u = avg μ ψ ρ k B M₀ u' u) :
    ∃ B', Char μ ρ ψ k B B' := by
  haveI := secondCountable_field F
  choose m hm using hst
  have hint : ∀ M u' u, IntegrableOn
      (fun x : Fin (k + 1) → F => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)) (lat F (k + 1) M)
      (Measure.pi fun _ => μ) := by
    intro M u' u
    refine ContinuousOn.integrableOn_compact (hlat M) (Continuous.continuousOn ?_)
    exact (hψ.comp (continuous_apply _).neg).mul (hcont u u')
  let f : V → V → ℂ := fun u' u => avg μ ψ ρ k B (m u u') u' u
  have hf : ∀ u' u M, m u u' ≤ M → f u' u = avg μ ψ ρ k B M u' u :=
    fun u' u M h => (hm u u' M h).symm
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) f ?_ ?_ ?_ ?_, ?_⟩
  · intro a b w
    let M := max (m w (a + b)) (max (m w a) (m w b))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a w) (hint M b w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a w
    let M := max (m w (c • a)) (m w a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro a v w
    let M := max (m (v + w) a) (max (m v a) (m w a))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a v) (hint M a w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a v
    let M := max (m (c • v) a) (m v a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    ring
  · intro u u'
    exact ⟨m u u', fun M hM => hf u' u M hM⟩

/- English proof (translation)
Introduce `h0 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hInv`. Take `⟨hψc, hL⟩` from `h0 F μ ψ hψ`. Establish `h4'` using `h4 F μ ψ hψ n V ρ hρ l k B hk hInv`. Use `exists_char μ ψ ρ k B hψc (fun M => ((hL (k + 1)).1 M).1) (fun u u' => (h4' u u').1) ?_` and prove the remaining obligations. Introduce `u u'`.

Take `⟨c, hc⟩` from `(h4' u u').2`. Use `⟨c + 1, fun M hM => ?_⟩` and prove the remaining obligations. Use `hc (scal F (k + 1) M) (div_scal_inv hM)` as an intermediate fact. Rewrite `this` using `[image_scal]`. Conclude with `this`.
-/
theorem stable_average : L0 → FormCoefficientStability → StableAverageExists := by
  intro h0 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hInv
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  have h4' := h4 F μ ψ hψ n V ρ hρ l k B hk hInv
  refine exists_char μ ψ ρ k B hψc (fun M => ((hL (k + 1)).1 M).1) (fun u u' => (h4' u u').1) ?_
  intro u u'
  obtain ⟨c, hc⟩ := (h4' u u').2
  refine ⟨c + 1, fun M hM => ?_⟩
  have := hc (scal F (k + 1) M) (div_scal_inv hM)
  rw [image_scal] at this
  exact this

end GlobalTheory.CompanionTheory.SatakeStable

end
