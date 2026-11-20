import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `N`. Establish `hN : I ^ N ≤ (J ^ N).comap j`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h N`. Conclude with `(hf N).comp (Ideal.quotientMap (J ^ N) j hN)`.
-/
private theorem adicCont_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] (j : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map j ≤ J) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J fun g => j (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap j := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h N
  exact (hf N).comp (Ideal.quotientMap (J ^ N) j hN)

/- English proof (translation)
Introduce `i k`. Use `⟨fun e => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations. Use `(h i k).1 e` as an intermediate fact. Rewrite `this`, the goal using `[Submodule.mem_bot]`. Simplify using `[this]`.
-/
private theorem od_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) R} (h : Z ∈ Od R R n a) : Z.map j ∈ Od S S n a := by
  intro i k
  refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
  have := (h i k).1 e
  rw [Submodule.mem_bot] at this ⊢
  simp [this]

/- English proof (translation)
Introduce `l _ F n x x' j hE`. Take `⟨⟨-, hloc, -, hρ, ha, -⟩, hw, -⟩` from `hE`. Establish `eρ : ∀ g, x'.ρX x'.A g = j.mapMatrix (x.ρX x.A g)`. Introduce `g`. Use extensionality with `i k : 1`.

Simplify using `only [NP.ρX, hρ]`. Both sides reduce to the same expression. Establish `ew : ∀ v, x'.wX x'.A v = j.mapMatrix (x.wX x.A v)`. Introduce `v`. Use extensionality with `i k : 1`.

Simplify using `only [NP.wX, hw]`. Both sides reduce to the same expression. Establish `ewi : ∀ v, x'.wiX x'.A v = j.mapMatrix (x.wiX x.A v)`. Introduce `v`. Use extensionality with `i k : 1`.

Simplify using `only [NP.wiX, hw, ← map_inv]`. Both sides reduce to the same expression. Establish `ed : ∀ Y g, dY F (x'.ρX x'.A) (Y.map j) g = j.mapMatrix (dY F (x.ρX x.A) Y g)`. Introduce `Y g`. Simplify using `only [dY, eρ, map_sub, map_mul]`.

Both sides reduce to the same expression. Establish `hL : ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y → LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j)`. Introduce `z v Y h g`. Establish `key : x'.wiX x'.A v * ((z (F.φ v g)).map j - dY F (x'.ρX x'.A) (Y.map j) (F.φ v g)) * x'.wX x'.A v = j.mapMatrix (x.wiX x.A v * (z (F.φ v g) - dY F (x.ρX x.A) Y (F.φ v g)) * x.wX x.A v)`. Rewrite using `[ed, ew, ewi, map_mul, map_mul, map_sub]`.

Both sides reduce to the same expression. Use `⟨fun i k hik => ?_, fun hg i => ?_⟩` and prove the remaining obligations. Simplify using `only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).1 i k hik, map_zero]`. Simplify using `only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).2 hg i, map_zero]`. Establish `ht : (Ideal.span {algebraMap x.A x.A x.t}).map j ≤ Ideal.span {algebraMap x'.A x'.A x'.t}`.

Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]`. Express the relevant statement in the definitionally equal form `(PowerSeries.X : PowerSeries x'.K) ∣ j PowerSeries.X`. Rewrite using `[PowerSeries.X_dvd_iff]`. Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (j PowerSeries.X)` using `PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne)`.

Establish `hX` using `PowerSeries.isUnit_iff_constantCoeff.1 (hloc.map_nonunit _ hu)`. Simplify using `at hX`. Use `⟨?_, ?_, hL⟩` and prove the remaining obligations. Introduce and unpack `z ⟨h1, h2, h3, h4, h5, h6⟩`. Use `⟨fun g => ha ▸ od_map j (h1 g), fun i k => adicCont_map j _ _ ht _ (h2 i k), fun g h => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `j.mapMatrix (z (g * h)) = j.mapMatrix (z g) + _ * j.mapMatrix (z h) * _`. Rewrite using `[h3, eρ, eρ, map_add, map_mul, map_mul]`. Use extensionality with `i k : 1`. Simplify using `[h4]`. Simplify using `[h5 u g hg]`.

Take `⟨Y, hY, hl⟩` from `h6 v`. Conclude with `⟨Y.map j, ha ▸ od_map j hY, hL z v Y hl⟩`. Introduce and unpack `z ⟨Y, hY, hT, rfl⟩`. Use `⟨Y.map j, ha ▸ od_map j hY, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.transpose_map, hT]`.

Use extensionality with `i k : 1`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `g`. Conclude with `(ed Y g).symm`.
-/
theorem UpperTheory.V.Pa.Det.pushSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → (∀ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)) ∧ (∀ z ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a)) ∧ ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y → LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
  intro l _ F n x x' j hE
  obtain ⟨⟨-, hloc, -, hρ, ha, -⟩, hw, -⟩ := hE
  have eρ : ∀ g, x'.ρX x'.A g = j.mapMatrix (x.ρX x.A g) := by
    intro g
    ext i k : 1
    simp only [NP.ρX, hρ]
    rfl
  have ew : ∀ v, x'.wX x'.A v = j.mapMatrix (x.wX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wX, hw]
    rfl
  have ewi : ∀ v, x'.wiX x'.A v = j.mapMatrix (x.wiX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have ed : ∀ Y g, dY F (x'.ρX x'.A) (Y.map j) g = j.mapMatrix (dY F (x.ρX x.A) Y g) := by
    intro Y g
    simp only [dY, eρ, map_sub, map_mul]
    rfl
  have hL : ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y →
      LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
    intro z v Y h g
    have key : x'.wiX x'.A v * ((z (F.φ v g)).map j - dY F (x'.ρX x'.A) (Y.map j) (F.φ v g)) * x'.wX x'.A v
        = j.mapMatrix (x.wiX x.A v * (z (F.φ v g) - dY F (x.ρX x.A) Y (F.φ v g)) * x.wX x.A v) := by
      rw [ed, ew, ewi, map_mul, map_mul, map_sub]
      rfl
    refine ⟨fun i k hik => ?_, fun hg i => ?_⟩
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).1 i k hik, map_zero]
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).2 hg i, map_zero]
  have ht : (Ideal.span {algebraMap x.A x.A x.t}).map j ≤ Ideal.span {algebraMap x'.A x'.A x'.t} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    change (PowerSeries.X : PowerSeries x'.K) ∣ j PowerSeries.X
    rw [PowerSeries.X_dvd_iff]
    by_contra hne
    have hu : IsUnit (j PowerSeries.X) := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne)
    have hX := PowerSeries.isUnit_iff_constantCoeff.1 (hloc.map_nonunit _ hu)
    simp at hX
  refine ⟨?_, ?_, hL⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => ha ▸ od_map j (h1 g), fun i k => adicCont_map j _ _ ht _ (h2 i k), fun g h => ?_,
      fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · change j.mapMatrix (z (g * h)) = j.mapMatrix (z g) + _ * j.mapMatrix (z h) * _
      rw [h3, eρ, eρ, map_add, map_mul, map_mul]
    · ext i k : 1
      simp [h4]
    · simp [h5 u g hg]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      exact ⟨Y.map j, ha ▸ od_map j hY, hL z v Y hl⟩
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map j, ha ▸ od_map j hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT]
      ext i k : 1
      simp
    · funext g
      exact (ed Y g).symm
