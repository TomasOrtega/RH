import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def stdForm (K : Type) [Field K] [StarRing K] (n : ℕ) :
    (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

def stdLat (K : Type) [Field K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdForm_apply (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Simplify using `[stdForm_apply, mul_comm, starRingEnd_apply]`.
-/
theorem stdForm_isSymm (K : Type) [Field K] [StarRing K] (n : ℕ) : (stdForm K n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp [stdForm_apply, mul_comm, starRingEnd_apply]

/- English proof (translation)
Use `⟨fun i => Pi.single i 1, ?_, ?_, rfl, ?_⟩` and prove the remaining obligations. Use `(Pi.basisFun K (Fin n)).linearIndependent` as an intermediate fact. Rewrite using `[show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from` and apply the resulting hypothesis. Use function extensionality and compare the values at `fun i => Pi.basisFun_apply K (Fin n) i] at this`. Use `(Pi.basisFun K (Fin n)).span_eq` as an intermediate fact.

Rewrite using `[show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from` and apply the resulting hypothesis. Use function extensionality and compare the values at `fun i => Pi.basisFun_apply K (Fin n) i] at this`. Introduce `i j`. Rewrite using `[stdForm_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Pi.single_apply]`. Simplify using `[Pi.single_apply, hij, Ne.symm hij]`.
-/
theorem stdLat_isOrtho (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (stdForm K n) (stdLat K n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, ?_⟩
  · have := (Pi.basisFun K (Fin n)).linearIndependent
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · have := (Pi.basisFun K (Fin n)).span_eq
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · intro i j
    rw [stdForm_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]

section Ortho

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

namespace StandardSymmetricSums

/- English proof (translation)
Simplify using `[map_sum, LinearMap.sum_apply, he, mul_comm, starRingEnd_apply]`.
-/
theorem form_sum {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (c d : Fin n → K) :
    h (∑ i, c i • e i) (∑ j, d j • e j) = ∑ i, star (c i) * d i := by
  simp [map_sum, LinearMap.sum_apply, he, mul_comm, starRingEnd_apply]

/- English proof (translation)
Simplify using `[map_sum, he]`.
-/
theorem form_left {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (i : Fin n) (d : Fin n → K) :
    h (e i) (∑ j, d j • e j) = d i := by
  simp [map_sum, he]

/- English proof (translation)
Assemble the required witnesses or components as `⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩`.
-/
theorem star_int (r : 𝓞 K) : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

/- English proof (translation)
The claim follows from `(Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)`.
-/
theorem exists_coord {n : ℕ} {e : Fin n → V} (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ c : Fin n → K, ∑ i, c i • e i = x :=
  (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)

/- English proof (translation)
Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Simplify using `only [algebraMap_smul]`.
-/
theorem mem_lat_iff {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]

end StandardSymmetricSums

open StandardSymmetricSums

/- English proof (translation)
Take `⟨e, hli, hsp, -, -⟩` from `hL`. Conclude with `(Basis.mk hli hsp.ge).finiteDimensional_of_finite`.
-/
theorem finiteDimensional_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : FiniteDimensional K V := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  exact (Basis.mk hli hsp.ge).finiteDimensional_of_finite

/- English proof (translation)
Take `⟨e, hli, hsp, -, -⟩` from `hL`. Simplify using `using finrank_eq_card_basis (Basis.mk hli hsp.ge)`.
-/
theorem finrank_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : finrank K V = n := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  simpa using finrank_eq_card_basis (Basis.mk hli hsp.ge)

/- English proof (translation)
Take `⟨e, hli, hsp, rfl, -⟩` from `hL`. Use `⟨Submodule.fg_span (Set.finite_range e), ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_span_of_tower, hsp]`.
-/
theorem isLattice_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Submodule.IsLattice K L := by
  obtain ⟨e, hli, hsp, rfl, -⟩ := hL
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, hsp]

/- English proof (translation)
Take `⟨e, hli, hsp, -, he⟩` from `hL`. Introduce `x hx φ`. Take `⟨c, rfl⟩` from `exists_coord hsp x`. Rewrite using `[form_sum he, map_sum, Complex.re_sum]`. Establish `hc : ∃ i, c i ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hx (by simp [hcon])`. Take `⟨i, hi⟩` from `hc`. Establish `hterm : ∀ j, (φ (star (c j) * c j)).re = Complex.normSq (φ (c j))`.

Introduce `j`. Rewrite using `[map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]`. Simplify using `only [hterm]`. Use `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Conclude with `Complex.normSq_pos.2 (by simpa using hi)`.
-/
theorem isTotPosDef_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    IsTotPosDef h := by
  obtain ⟨e, hli, hsp, -, he⟩ := hL
  intro x hx φ
  obtain ⟨c, rfl⟩ := exists_coord hsp x
  rw [form_sum he, map_sum, Complex.re_sum]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (by simp [hcon])
  obtain ⟨i, hi⟩ := hc
  have hterm : ∀ j, (φ (star (c j) * c j)).re = Complex.normSq (φ (c j)) := by
    intro j
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]
  simp only [hterm]
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 (by simpa using hi)

/- English proof (translation)
Introduce `x hx`. Establish `hp` using `isTotPosDef_of_ortho hK hs hL x hx`. Establish `ht` using `trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)`. Establish `hre` using `congrArg Complex.re ht`. Rewrite `hre` using `[Complex.re_sum]`.

Establish `hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re` using `Finset.sum_pos (fun σ _ => hp σ.toRingHom) ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩`. Rewrite `hpos` using `[← hre]`. Establish `: (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)`. Simplify using the standard rewrite rules. Rewrite `hpos` using `[this]`.

Conclude with `hpos` after adjusting the coercions.
-/
theorem trace_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := isTotPosDef_of_ortho hK hs hL x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

/- English proof (translation)
Take `⟨e, hli, hsp, rfl, he⟩` from `hL`. Introduce `x hx y hy`. Take `⟨c, rfl⟩` from `(mem_lat_iff x).1 hx`. Take `⟨d, rfl⟩` from `(mem_lat_iff y).1 hy`. Rewrite using `[form_sum he]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `star_int (c i)`. Rewrite using `[← ht, ← map_mul]`. Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`.
-/
theorem isIntegralLat_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨c, rfl⟩ := (mem_lat_iff x).1 hx
  obtain ⟨d, rfl⟩ := (mem_lat_iff y).1 hy
  rw [form_sum he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := star_int (c i)
  rw [← ht, ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

/- English proof (translation)
Establish `hint` using `isIntegralLat_of_ortho hL`. Take `⟨e, hli, hsp, rfl, he⟩` from `hL`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨c, rfl⟩` from `exists_coord hsp x`.

Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at hx`. Establish `hc : ∀ i, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c i`. Introduce `i`. Use `hx (e i) (Submodule.subset_span ⟨i, rfl⟩)` as an intermediate fact. Rewrite `this` using `[form_left he]`.

Conclude with `Submodule.mem_one.1 this`. Use `choose r hr using hc`. Conclude with `(mem_lat_iff _).2 ⟨r, by simp only [hr]⟩`. Introduce `x hx`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`.

Conclude with `fun y hy => hint y hy x hx`.
-/
theorem isUnimodular_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsUnimodular h L := by
  have hint := isIntegralLat_of_ortho hL
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := exists_coord hsp x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars] at hx
    have hc : ∀ i, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c i := by
      intro i
      have := hx (e i) (Submodule.subset_span ⟨i, rfl⟩)
      rw [form_left he] at this
      exact Submodule.mem_one.1 this
    choose r hr using hc
    exact (mem_lat_iff _).2 ⟨r, by simp only [hr]⟩
  · intro x hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars]
    exact fun y hy => hint y hy x hx

/- English proof (translation)
The claim follows from `((Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => (star_int r).imp fun _ ht => ht) L (isLattice_of_ortho hL).fg).2).1 (isUnimodular_of_ortho hL)`.
-/
theorem isUnimodularAt_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L :=
  ((Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => (star_int r).imp fun _ ht => ht) L
    (isLattice_of_ortho hL).fg).2).1 (isUnimodular_of_ortho hL)

end Ortho

end Formalism.HermitianLattices.Ext.L3
