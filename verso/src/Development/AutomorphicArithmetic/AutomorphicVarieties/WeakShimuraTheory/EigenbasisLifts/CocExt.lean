import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[map_mul, F.η_c]`. Break down `Int.units_eq_one_or (F.η x) with h | h` into its components or cases. Conclude with `absurd h hx`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
private theorem cocExt_mem {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {x : F.Γ} (hx : x ∉ F.η.ker) : x * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η x) with h | h
  · exact absurd h hx
  · rw [h]
    rfl

/- English proof (translation)
Establish `hcc : F.c * F.c = 1` using `F.c_sq`. Establish `hci : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right hcc`. Establish `hc2 : ∀ x : F.Γ, x * F.c * F.c = x` using `fun x => by rw [mul_assoc, hcc, mul_one]`. Establish `I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c` using `fun g h => by`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc F.c F.c, hcc, one_mul]`. Establish `I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h` using `fun g h => by`. Simplify using `only [mul_assoc]`. Rewrite using `[hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]`. Establish `hker : IsOpen (F.η.ker : Set F.Γ)` using `F.η_open`.

Establish `hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ` using `(Subgroup.isClosed_of_isOpen _ hker).isOpen_compl`. Establish `Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v)` using `fun a b v => by rw [map_mul]; rfl`. Establish `hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c` using `fun k => by`. Simplify using `[W.GFrame.conj, hci]`. Establish `hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1` using `fun x hx => by`.

Break down `Int.units_eq_one_or (F.η x) with h | h` into its components or cases. Conclude with `absurd (MonoidHom.mem_ker.mpr h) hx`. Conclude with `h`. Set `z : F.Γ → M` to `fun x => if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w`. Establish `zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩` using `fun x hx => dif_pos hx`.

Establish `zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w` using `fun x hx => dif_neg hx`. Use `⟨z, ?_, ?_, fun g => zin g g.2⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ F.η.ker`.

Apply `ContinuousOn.continuousAt _ (hker.mem_nhds hx)` to reduce the goal to its premises. Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀)` using `continuous_subtype_val.subtype_mk fun p => p.2`. Use `(hy.comp hm).congr fun p => ?_` and prove the remaining obligations. Conclude with `(zin p.1 p.2).symm`.

Apply `ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)` to reduce the goal to its premises. Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀)` using `(continuous_subtype_val.mul continuous_const).subtype_mk _`. Use `((hy.comp hm).add (hw.comp hm)).congr fun p => ?_` and prove the remaining obligations. Conclude with `(zout p.1 p.2).symm`.

Introduce `g h`. Apply the tactic sequence `by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker`. Rewrite using `[zin _ (mul_mem hg hh), zin _ hg, zin _ hh]`. Conclude with `hyc ⟨g, hg⟩ ⟨h, hh⟩`. Establish `hgh : g * h ∉ F.η.ker` using `fun H => hh (by simpa using mul_mem (inv_mem hg) H)`.

Rewrite using `[zout _ hgh, zin _ hg, zout _ hh]`. Establish `e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩` using `Subtype.ext (mul_assoc _ _ _)`. Rewrite using `[e, hyc, map_add, ← Rm, ← mul_assoc]`. Conclude with `add_assoc _ _ _`. Establish `hgh : g * h ∉ F.η.ker` using `fun H => hg (by simpa using mul_mem H (inv_mem hh))`.

Rewrite using `[zout _ hgh, zout _ hg, zin _ hh]`. Establish `e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)`. Rewrite using `[hconj]`.

Conclude with `(I1 g h).symm`. Rewrite using `[e, hyc, hrel, map_add, map_sub]`. Establish `e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩)`. Rewrite using `[← Rm]`. Use `show R (g * F.c * F.c) _ = _`.

Rewrite using `[hc2]`. Establish `e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w`. Rewrite using `[← Rm, hconj]`. Use `show R (g * F.c * (F.c * h * F.c)) w = _`. Rewrite using `[I1]`.

Rewrite using `[e1, e2]`. Use `show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _`. Normalize the expressions using the abelian group laws. Establish `hgh : g * h ∈ F.η.ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]`.

Evaluate the decidable proposition. Rewrite using `[zin _ hgh, zout _ hg, zout _ hh]`. Establish `e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)`.

Rewrite using `[hconj]`. Conclude with `(I2 g h).symm`. Rewrite using `[e, hyc, hrel, map_add, map_sub, map_add]`. Establish `e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) = R g (y ⟨h * F.c, cocExt_mem F hh⟩)`. Rewrite using `[← Rm]`.

Use `show R (g * F.c * F.c) _ = _`. Rewrite using `[hc2]`. Establish `e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) = -R g (R (h * F.c) w)`. Rewrite using `[← Rm, hconj]`. Use `show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _`.

Rewrite using `[I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]`. Rewrite using `[e1, e2]`. Use `show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))`. Normalize the expressions using the abelian group laws.
-/
private theorem cocycle_extends_to_conj_group {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K M : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (R : Representation K F.Γ M) (y : F.G₀ → M) (w : M)
    (hy : Continuous y) (hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h))
    (hw : Continuous fun g : F.G₀ => R g w) (hcw : R F.c w = -w)
    (hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)) :
    ∃ z : F.Γ → M, Continuous z ∧ (∀ g h, z (g * h) = z g + R g (z h)) ∧ ∀ g : F.G₀, z g = y g := by
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hc2 : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, hcc, mul_one]
  have I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c := fun g h => by
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hcc, one_mul]
  have I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h := fun g h => by
    simp only [mul_assoc]
    rw [hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]
  have hker : IsOpen (F.η.ker : Set F.Γ) := F.η_open
  have hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ := (Subgroup.isClosed_of_isOpen _ hker).isOpen_compl
  have Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v) := fun a b v => by rw [map_mul]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1 := fun x hx => by
    rcases Int.units_eq_one_or (F.η x) with h | h
    · exact absurd (MonoidHom.mem_ker.mpr h) hx
    · exact h
  let z : F.Γ → M := fun x =>
    if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w
  have zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩ := fun x hx => dif_pos hx
  have zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w :=
    fun x hx => dif_neg hx
  refine ⟨z, ?_, ?_, fun g => zin g g.2⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.η.ker
    · apply ContinuousOn.continuousAt _ (hker.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀) :=
        continuous_subtype_val.subtype_mk fun p => p.2
      refine (hy.comp hm).congr fun p => ?_
      exact (zin p.1 p.2).symm
    · apply ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀) :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      refine ((hy.comp hm).add (hw.comp hm)).congr fun p => ?_
      exact (zout p.1 p.2).symm
  · intro g h
    by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker
    · rw [zin _ (mul_mem hg hh), zin _ hg, zin _ hh]
      exact hyc ⟨g, hg⟩ ⟨h, hh⟩
    · have hgh : g * h ∉ F.η.ker := fun H => hh (by simpa using mul_mem (inv_mem hg) H)
      rw [zout _ hgh, zin _ hg, zout _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩ :=
        Subtype.ext (mul_assoc _ _ _)
      rw [e, hyc, map_add, ← Rm, ← mul_assoc]
      exact add_assoc _ _ _
    · have hgh : g * h ∉ F.η.ker := fun H => hg (by simpa using mul_mem H (inv_mem hh))
      rw [zout _ hgh, zout _ hg, zin _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩ := by
        apply Subtype.ext
        show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I1 g h).symm
      rw [e, hyc, hrel, map_add, map_sub]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * h * F.c)) w = _
        rw [I1]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _
      abel
    · have hgh : g * h ∈ F.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]
        decide
      rw [zin _ hgh, zout _ hg, zout _ hh]
      have e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩ := by
        apply Subtype.ext
        show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I2 g h).symm
      rw [e, hyc, hrel, map_add, map_sub, map_add]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) =
          R g (y ⟨h * F.c, cocExt_mem F hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) =
          -R g (R (h * F.c) w) := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _
        rw [I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))
      abel

/- English proof (translation)
Introduce `l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ`. Take `⟨hy0, hycoc⟩` from `hy`. Establish `hcc : F.c * F.c = 1` using `F.c_sq`. Establish `hci : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right hcc`. Establish `Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v)` using `fun a b v => by rw [map_mul]; rfl`.

Establish `Rcc : ∀ v, R F.c (R F.c v) = v` using `fun v => by rw [← Rm, hcc, map_one]; rfl`. Establish `hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c` using `fun k => by`. Simplify using `[W.GFrame.conj, hci]`. Establish `cc : ∀ g : F.G₀, F.conj (F.conj g) = g` using `fun g => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hconj, hconj]`. Simplify using `only [← mul_assoc, hcc, one_mul]`. Rewrite using `[mul_assoc, hcc, mul_one]`. Establish `hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h)` using `fun g h => by`. Rewrite using `[hycoc g h, hA.ad]`.

Establish `hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z`. Introduce `g`. Establish `e2` using `hZ (F.conj g)`. Rewrite `e2` using `[cc, hZ g, map_add, Rcc, map_sub, ← Rm, hconj]`. Establish `ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c`.

Rewrite using `[← mul_assoc, ← mul_assoc, hcc, one_mul]`. Rewrite `e2` using `[ec, Rm]`. Rewrite using `[map_add, ← sub_eq_zero, ← neg_eq_zero]`. Rewrite `e2` using `[← sub_eq_zero]`. Rewrite using `[← e2]`.

Normalize the expressions using the abelian group laws. Use `set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef`. Establish `hcw : R F.c w = -w`. Rewrite using `[hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]`. Establish `hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)`.

Introduce `g`. Rewrite using `[hZ g]`. Use `congr 1`. Establish `hi` using `hinv (F.conj g)`. Rewrite `hi` using `[map_add]`.

Rewrite using `[hwdef, map_smul, map_sub, ← smul_sub]`. Establish `hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z`. Rewrite using `[← hi]`. Normalize the expressions using the abelian group laws. Rewrite using `[hb]`.

Establish `e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) = (2 : K) • (R (↑(F.conj g)) Z - Z)`. Rewrite using `[two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]`. Establish `hw : Continuous fun g : F.G₀ => R g w`.

Establish `e : (fun g : F.G₀ => R g w) = fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)`. Use function extensionality and compare the values at `fun g => by rw [hA.ad]; rfl`. Rewrite using `[e]`. Conclude with `((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)`. Take `⟨z, hz, hzc, hzy⟩` from `cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel`.

Conclude with `⟨z, ⟨hz, hzc⟩, hzy⟩`.
-/
theorem UpperTheory.V.Ws.Eb.cocExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)), Full ρ → Continuous ρ → IsAdExt F ρ P R →
        ∀ y ∈ Z1 (Loc.adGL ρ), ∀ Z, (∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z)) → ∃ z ∈ Z1 R, ∀ g : F.G₀, z g = y g := by
  intro l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ
  obtain ⟨hy0, hycoc⟩ := hy
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v) :=
    fun a b v => by rw [map_mul]; rfl
  have Rcc : ∀ v, R F.c (R F.c v) = v := fun v => by rw [← Rm, hcc, map_one]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have cc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    rw [hconj, hconj]
    simp only [← mul_assoc, hcc, one_mul]
    rw [mul_assoc, hcc, mul_one]
  have hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h) := fun g h => by
    rw [hycoc g h, hA.ad]
  have hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z := by
    intro g
    have e2 := hZ (F.conj g)
    rw [cc, hZ g, map_add, Rcc, map_sub, ← Rm, hconj] at e2
    have ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c := by
      rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
    rw [ec, Rm] at e2
    rw [map_add, ← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at e2
    rw [← e2]
    abel
  set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef
  have hcw : R F.c w = -w := by
    rw [hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]
  have hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w) := by
    intro g
    rw [hZ g]
    congr 1
    have hi := hinv (F.conj g)
    rw [map_add] at hi
    rw [hwdef, map_smul, map_sub, ← smul_sub]
    have hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z := by
      rw [← hi]
      abel
    rw [hb]
    have e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) =
        (2 : K) • (R (↑(F.conj g)) Z - Z) := by
      rw [two_smul]
      abel
    rw [e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hw : Continuous fun g : F.G₀ => R g w := by
    have e : (fun g : F.G₀ => R g w) =
        fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
      funext fun g => by rw [hA.ad]; rfl
    rw [e]
    exact ((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)
  obtain ⟨z, hz, hzc, hzy⟩ := cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel
  exact ⟨z, ⟨hz, hzc⟩, hzy⟩
