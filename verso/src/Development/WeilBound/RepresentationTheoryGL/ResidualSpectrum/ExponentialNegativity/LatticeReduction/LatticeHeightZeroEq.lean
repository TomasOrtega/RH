import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsFF

noncomputable section

open Matrix Module

namespace PositivityTheory.Rg.Rs.JLatOf

open PositivityTheory.Rg.Rs

variable {k : Type} [Field k] {N : ℕ}

def Mj (k : Type) [Field k] (N j : ℕ) : Submodule k (Fin N → k) where
  carrier := {x | ∀ a : Fin N, (a : ℕ) < j → x a = 0}
  add_mem' := by
    intro x y hx hy a ha
    simp [hx a ha, hy a ha]
  zero_mem' := by
    intro a _
    rfl
  smul_mem' := by
    intro c x hx a ha
    simp [hx a ha]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_Mj {j : ℕ} {x : Fin N → k} : x ∈ Mj k N j ↔ ∀ a : Fin N, (a : ℕ) < j → x a = 0 := by
  exact Iff.rfl

/- English proof (translation)
Use `eq_top_iff.mpr (fun x _ => ?_)` and prove the remaining obligations. Introduce `a ha`. Conclude with `absurd ha (Nat.not_lt_zero _)`.
-/
theorem Mj_zero : Mj k N 0 = ⊤ := by
  refine eq_top_iff.mpr (fun x _ => ?_)
  intro a ha
  exact absurd ha (Nat.not_lt_zero _)

/- English proof (translation)
Use `delta gmap`. Simplify using `only [Submodule.mem_map, Matrix.toLin'_apply]`.
-/
theorem mem_gmap {g : GL (Fin N) k} {M : Submodule k (Fin N → k)} {y : Fin N → k} :
    y ∈ gmap g M ↔ ∃ x ∈ M, (g : Matrix (Fin N) (Fin N) k) *ᵥ x = y := by
  delta gmap
  simp only [Submodule.mem_map, Matrix.toLin'_apply]

/- English proof (translation)
Use `delta gmap`. Simplify using `only [Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]`.
-/
theorem gmap_mul (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) : gmap (g * h) M = gmap g (gmap h M) := by
  delta gmap
  simp only [Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

/- English proof (translation)
Use `delta gmap`. Simplify using the standard rewrite rules.
-/
theorem gmap_one (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  delta gmap
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h1 conv_rhs => rw [← h1]`. Rewrite using `[← gmap_mul, mul_inv_cancel_left]`. Introduce `h1`. Rewrite using `[gmap_mul, h1, ← gmap_mul, inv_mul_cancel, gmap_one]`.
-/
theorem gmap_inv_mul_eq_iff (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g⁻¹ * h) M = M ↔ gmap h M = gmap g M := by
  constructor
  · intro h1
    conv_rhs => rw [← h1]
    rw [← gmap_mul, mul_inv_cancel_left]
  · intro h1
    rw [gmap_mul, h1, ← gmap_mul, inv_mul_cancel, gmap_one]

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))`. Introduce `x y hxy`. Establish `h2` using `congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy`. Simplify `h2` using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec]`. Conclude with `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj M)).symm`.
-/
theorem finrank_gmap (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    finrank k (gmap g M) = finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin N) (Fin N) k)) := by
    intro x y hxy
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h2
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj M)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hle a b ha hb`. Establish `hmem : (Pi.single b 1 : Fin N → k) ∈ Mj k N j`. Introduce `a' ha'`. Establish `hne : a' ≠ b`.

Introduce `he`. Rewrite `ha'` using `[he]`. Use linear arithmetic over natural numbers and integers. Simplify using `[Pi.single_apply, hne]`. Establish `h2` using `hle (mem_gmap.mpr ⟨_, hmem, rfl⟩) a ha`.

Simplify `h2` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Introduce `hz y hy`. Take `⟨x, hx, rfl⟩` from `mem_gmap.mp hy`. Introduce `a ha`. Use `show ∑ b : Fin N, (g : Matrix (Fin N) (Fin N) k) a b * x b = 0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Distinguish the cases in `hb : (b : ℕ) < j`. Rewrite using `[hx b hb, mul_zero]`. Rewrite using `[hz a b ha (by omega), zero_mul]`.
-/
theorem gmap_le_Mj_iff (g : GL (Fin N) k) (j : ℕ) :
    gmap g (Mj k N j) ≤ Mj k N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hle a b ha hb
    have hmem : (Pi.single b 1 : Fin N → k) ∈ Mj k N j := by
      intro a' ha'
      have hne : a' ≠ b := by
        intro he
        rw [he] at ha'
        omega
      simp [Pi.single_apply, hne]
    have h2 := hle (mem_gmap.mpr ⟨_, hmem, rfl⟩) a ha
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2
  · intro hz y hy
    obtain ⟨x, hx, rfl⟩ := mem_gmap.mp hy
    intro a ha
    show ∑ b : Fin N, (g : Matrix (Fin N) (Fin N) k) a b * x b = 0
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : (b : ℕ) < j
    · rw [hx b hb, mul_zero]
    · rw [hz a b ha (by omega), zero_mul]

/- English proof (translation)
Establish `hmem : g ∈ Formalism.UG.P.tjcosets_par N j ↔ ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0` using `Iff.rfl`. Rewrite using `[hmem, ← gmap_le_Mj_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hle`. Conclude with `Submodule.eq_of_le_of_finrank_eq hle (finrank_gmap g _)`.

Introduce `heq`. Conclude with `heq.le`.
-/
theorem mem_par_iff [Finite k] (g : GL (Fin N) k) (j : ℕ) :
    g ∈ Formalism.UG.P.tjcosets_par N j ↔ gmap g (Mj k N j) = Mj k N j := by
  have hmem : g ∈ Formalism.UG.P.tjcosets_par N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := Iff.rfl
  rw [hmem, ← gmap_le_Mj_iff]
  constructor
  · intro hle
    exact Submodule.eq_of_le_of_finrank_eq hle (finrank_gmap g _)
  · intro heq
    exact heq.le

def ej (N j m : ℕ) (h : m + j = N) (i : Fin m) : Fin N → k := Pi.single (⟨j + i, by omega⟩ : Fin N) 1

/- English proof (translation)
Establish `hf : Function.Injective (fun i : Fin m => (⟨j + i, by omega⟩ : Fin N))`. Introduce `a b hab`. Simplify using `only [Fin.mk.injEq] at hab`. Conclude with `Fin.ext (by omega)`. Establish `h2` using `(Pi.basisFun k (Fin N)).linearIndependent.comp _ hf`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[ej]`.
-/
theorem linInd_ej (N j m : ℕ) (h : m + j = N) : LinearIndependent k (ej (k := k) N j m h) := by
  have hf : Function.Injective (fun i : Fin m => (⟨j + i, by omega⟩ : Fin N)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have h2 := (Pi.basisFun k (Fin N)).linearIndependent.comp _ hf
  convert h2 using 1
  funext i
  simp [ej]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : x = ∑ i : Fin m, x ⟨j + i, by omega⟩ • ej (k` using `k) N j m h i := by`. Use extensionality with `a`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, ej, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`.

Distinguish the cases in `ha : (a : ℕ) < j`. Rewrite using `[hx a ha]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[if_neg]`. Introduce `hai`. Rewrite `ha` using `[hai]`. Simplify using `at ha`. Rewrite using `[Finset.sum_eq_single (⟨(a : ℕ) - j, by omega⟩ : Fin m)]`.

Rewrite using `[if_pos (Fin.ext (by simp; omega))]`. Use `congr 1`. Conclude with `Fin.ext (by simp; omega)`. Introduce `i _ hi`. Rewrite using `[if_neg]`.

Introduce `hai`. Apply `hi` to reduce the goal to its premises. Establish `h3` using `congrArg Fin.val hai`. Simplify using `at h3`. Conclude with `Fin.ext (by simp; omega)`.

Introduce `hne`. Conclude with `absurd (Finset.mem_univ _) hne`. Rewrite using `[hx']`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩ a ha`. Establish `hne : a ≠ ⟨j + i, by omega⟩`. Introduce `he`. Rewrite `ha` using `[he]`. Simplify using `at ha`.

Simplify using `[ej, Pi.single_apply, hne]`.
-/
theorem Mj_eq_span (N j m : ℕ) (h : m + j = N) :
    Mj k N j = Submodule.span k (Set.range (ej (k := k) N j m h)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i : Fin m, x ⟨j + i, by omega⟩ • ej (k := k) N j m h i := by
      ext a
      simp only [Finset.sum_apply, Pi.smul_apply, ej, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases ha : (a : ℕ) < j
      · rw [hx a ha]
        symm
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro hai
        rw [hai] at ha
        simp at ha
      · rw [Finset.sum_eq_single (⟨(a : ℕ) - j, by omega⟩ : Fin m)]
        · rw [if_pos (Fin.ext (by simp; omega))]
          congr 1
          exact Fin.ext (by simp; omega)
        · intro i _ hi
          rw [if_neg]
          intro hai
          apply hi
          have h3 := congrArg Fin.val hai
          simp at h3
          exact Fin.ext (by simp; omega)
        · intro hne
          exact absurd (Finset.mem_univ _) hne
    rw [hx']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ a ha
    have hne : a ≠ ⟨j + i, by omega⟩ := by
      intro he
      rw [he] at ha
      simp at ha
    simp [ej, Pi.single_apply, hne]

/- English proof (translation)
Rewrite using `[Mj_eq_span N j (N - j) (by omega), finrank_span_eq_card (linInd_ej N j (N - j) (by omega))]`. Simplify using the standard rewrite rules.
-/
theorem finrank_Mj (N j : ℕ) (h : j ≤ N) : finrank k (Mj k N j) = N - j := by
  rw [Mj_eq_span N j (N - j) (by omega), finrank_span_eq_card (linInd_ej N j (N - j) (by omega))]
  simp

/- English proof (translation)
Use `delta gmap`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem gmap_span {ι : Type} (g : GL (Fin N) k) (u : ι → Fin N → k) :
    gmap g (Submodule.span k (Set.range u)) =
      Submodule.span k (Set.range fun i => (g : Matrix (Fin N) (Fin N) k) *ᵥ u i) := by
  delta gmap
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

/- English proof (translation)
Establish `h1 : Set.range (fun i => (b i : Fin N → k)) = M.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem span_basis_coe {ι : Type} {M : Submodule k (Fin N → k)} (b : Basis ι k M) :
    Submodule.span k (Set.range fun i => (b i : Fin N → k)) = M := by
  have h1 : Set.range (fun i => (b i : Fin N → k)) = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Substitute `h` using the available equality. Establish `hm : m + j - j = m` using `by omega`. Set `w : Formalism.UG.P.TjcosetsFr (m + j - j) (m + j) k` to `fun i => u (Fin.cast hm i)`. Establish `hw : LinearIndependent k w` using `hu.comp _ (Fin.cast_injective hm)`. Take `⟨g, hg⟩` from `Formalism.UG.P.tjcosets_exists_smul (m + j) j w hw`.

Use `⟨g, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun hg (Fin.cast hm.symm i)`. Rewrite `h1` using `[Formalism.UG.P.GL_smul_standard_tuple]`. Establish `h2 : w (Fin.cast hm.symm i) = u i`. Simplify using `only [w]`.

Use `congr 1`. Rewrite using `[← h2, ← h1]`. Use extensionality with `a`. Apply the tactic sequence `(simp [ej, Matrix.mulVec, dotProduct, Pi.single_apply]) <;> rfl`.
-/
theorem exists_frame [Finite k] (N j m : ℕ) (h : m + j = N) (u : Fin m → Fin N → k) (hu : LinearIndependent k u) :
    ∃ g : GL (Fin N) k, ∀ i : Fin m, (g : Matrix (Fin N) (Fin N) k) *ᵥ ej N j m h i = u i := by
  subst h
  have hm : m + j - j = m := by omega
  let w : Formalism.UG.P.TjcosetsFr (m + j - j) (m + j) k := fun i => u (Fin.cast hm i)
  have hw : LinearIndependent k w := hu.comp _ (Fin.cast_injective hm)
  obtain ⟨g, hg⟩ := Formalism.UG.P.tjcosets_exists_smul (m + j) j w hw
  refine ⟨g, fun i => ?_⟩
  have h1 := congrFun hg (Fin.cast hm.symm i)
  rw [Formalism.UG.P.GL_smul_standard_tuple] at h1
  have h2 : w (Fin.cast hm.symm i) = u i := by
    simp only [w]
    congr 1
  rw [← h2, ← h1]
  ext a
  (simp [ej, Matrix.mulVec, dotProduct, Pi.single_apply]) <;> rfl

/- English proof (translation)
Set `b` to `Module.finBasis k M`. Establish `hli : LinearIndependent k (fun i => (b i : Fin N → k))` using `b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Take `⟨g, hg⟩` from `exists_frame N j (finrank k M) h (fun i => (b i : Fin N → k)) hli`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[Mj_eq_span N j _ h, gmap_span]`.

Simplify using `only [hg]`. Conclude with `span_basis_coe b`.
-/
theorem exists_gmap_Mj [Finite k] (M : Submodule k (Fin N → k)) (j : ℕ) (h : finrank k M + j = N) :
    ∃ g : GL (Fin N) k, gmap g (Mj k N j) = M := by
  let b := Module.finBasis k M
  have hli : LinearIndependent k (fun i => (b i : Fin N → k)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  obtain ⟨g, hg⟩ := exists_frame N j (finrank k M) h (fun i => (b i : Fin N → k)) hli
  refine ⟨g, ?_⟩
  rw [Mj_eq_span N j _ h, gmap_span]
  simp only [hg]
  exact span_basis_coe b

/- English proof (translation)
Establish `hcol : (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 = (g : Matrix (Fin N) (Fin N) k) i₀ i₀ • (Pi.single i₀ 1 : Fin N → k)`. Use extensionality with `a`. Distinguish the cases in `ha : a = i₀`. Substitute `ha` using the available equality. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, ha, h0 a ha]`. Establish `hc : (g : Matrix (Fin N) (Fin N) k) i₀ i₀ ≠ 0`. Introduce `hc`. Rewrite `hcol` using `[hc, zero_smul]`. Establish `hinj : Function.Injective (fun v : Fin N → k => (g : Matrix (Fin N) (Fin N) k) *ᵥ v)`.

Introduce `x y hxy`. Establish `h2` using `congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy`. Simplify `h2` using `[Matrix.mulVec_mulVec]`. Establish `h3 : (Pi.single i₀ (1 : k) : Fin N → k) = 0` using `hinj (by show (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 = (g : Matrix (Fin N) (Fin N) k) *ᵥ 0`. Rewrite using `[hcol, Matrix.mulVec_zero])`.

Establish `h4` using `congrFun h3 i₀`. Simplify using `at h4`. Use `delta gmap`. Rewrite using `[Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hcol, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]`.
-/
theorem gmap_line (g : GL (Fin N) k) (i₀ : Fin N) (h0 : ∀ a, a ≠ i₀ → (g : Matrix (Fin N) (Fin N) k) a i₀ = 0) :
    gmap g (Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)}) =
      Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)} := by
  have hcol : (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 =
      (g : Matrix (Fin N) (Fin N) k) i₀ i₀ • (Pi.single i₀ 1 : Fin N → k) := by
    ext a
    by_cases ha : a = i₀
    · subst ha
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, ha, h0 a ha]
  have hc : (g : Matrix (Fin N) (Fin N) k) i₀ i₀ ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hcol
    have hinj : Function.Injective (fun v : Fin N → k => (g : Matrix (Fin N) (Fin N) k) *ᵥ v) := by
      intro x y hxy
      have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec] using h2
    have h3 : (Pi.single i₀ (1 : k) : Fin N → k) = 0 := hinj (by
      show (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 = (g : Matrix (Fin N) (Fin N) k) *ᵥ 0
      rw [hcol, Matrix.mulVec_zero])
    have h4 := congrFun h3 i₀
    simp at h4
  delta gmap
  rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hcol,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]

/- English proof (translation)
Use extensionality with `x`. Use `delta H0`. Simplify using `only [LinearMap.mem_ker, LinearMap.proj_apply, mem_Mj]`. Prove the components needed by the constructor for the conclusion. Introduce `hx a ha`.

Establish `ha0 : a = 0` using `Fin.ext (Nat.lt_one_iff.mp ha)`. Rewrite using `[ha0]`. Conclude with `hx`. Introduce `hx`. Conclude with `hx 0 (by simp)`.
-/
theorem lattice_height_zero_eq (n : ℕ) : H0 k n = Mj k (n + 1) 1 := by
  ext x
  delta H0
  simp only [LinearMap.mem_ker, LinearMap.proj_apply, mem_Mj]
  constructor
  · intro hx a ha
    have ha0 : a = 0 := Fin.ext (Nat.lt_one_iff.mp ha)
    rw [ha0]
    exact hx
  · intro hx
    exact hx 0 (by simp)

/- English proof (translation)
Take `⟨r, hr⟩ : ∃ r, r = finrank k M` from `⟨_, rfl⟩`. Establish `hr1 : 1 ≤ r`. Rewrite using `[hr, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]`. Introduce `hbot`. Rewrite `hM` using `[hbot, Submodule.mem_bot]`.

Establish `h5 : (Pi.single (0 : Fin (n + 1)) (1 : k) : Fin (n + 1) → k) 0 = 0` using `congrFun hM 0`. Simplify using `at h5`. Establish `hrle : r ≤ n + 1`. Rewrite using `[hr]`. Conclude with `(Submodule.finrank_le M).trans (by simp)`.

Establish `hH0 : finrank k (H0 k n) = n`. Rewrite using `[lattice_height_zero_eq, finrank_Mj _ _ (by omega)]`. Simplify using the standard rewrite rules. Establish `hsup : M ⊔ H0 k n = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hx : x = x 0 • e0 k n + (x - x 0 • e0 k n)` using `by abel`. Rewrite using `[hx]`. Apply `Submodule.add_mem_sup (Submodule.smul_mem _ _ hM)` to reduce the goal to its premises. Use `delta H0 e0`.

Simplify using the standard rewrite rules. Establish `hdim` using `Submodule.finrank_sup_add_finrank_inf_eq M (H0 k n)`. Rewrite `hdim` using `[hsup, finrank_top, Module.finrank_fin_fun, hH0, ← hr]`. Take `⟨m, hm⟩ : ∃ m, m = r - 1` from `⟨_, rfl⟩`. Take `⟨P, hP⟩ : ∃ P : Submodule k (Fin (n + 1) → k), P = M ⊓ H0 k n` from `⟨_, rfl⟩`.

Rewrite `hdim` using `[← hP]`. Establish `hdimMH : finrank k ↥P = m` using `by omega`. Take `⟨b⟩ : Nonempty (Basis (Fin m) k ↥P)` from `⟨Module.finBasisOfFinrankEq k _ hdimMH⟩`. Take `⟨v, hv_def⟩ : ∃ v : Fin m → Fin (n + 1) → k, v = fun i => (b i : Fin (n + 1) → k)` from `⟨_, rfl⟩`. Take `⟨u, hu_def⟩ : ∃ u : Fin (m + 1) → Fin (n + 1) → k, u = Fin.cons (e0 k n) v` from `⟨_, rfl⟩`.

Establish `hvli : LinearIndependent k v`. Rewrite using `[hv_def]`. Conclude with `b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)`. Establish `hspanv : Submodule.span k (Set.range v) = M ⊓ H0 k n`. Rewrite using `[hv_def, ← hP]`.

Conclude with `span_basis_coe b`. Establish `hvmem : ∀ i, v i ∈ M ⊓ H0 k n`. Introduce `i`. Rewrite using `[hv_def, ← hP]`. Conclude with `(b i).2`.

Establish `he0 : e0 k n ∉ H0 k n` using `by delta H0 e0`. Simplify using the standard rewrite rules. Establish `hu : LinearIndependent k u`. Rewrite using `[hu_def, linearIndependent_finCons]`. Use `⟨hvli, ?_⟩` and prove the remaining obligations.

Rewrite using `[hspanv]`. Introduce `hmem`. Conclude with `he0 (Submodule.mem_inf.mp hmem).2`. Establish `hsum : (m + 1) + (n + 1 - r) = n + 1` using `by omega`. Take `⟨g, hg⟩` from `exists_frame (n + 1) (n + 1 - r) (m + 1) hsum u hu`.

Use `⟨⟨n + 1 - r, by omega⟩, g, by simp only; omega, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show gmap g (Mj k (n + 1) (n + 1 - r)) = M`. Rewrite using `[Mj_eq_span (n + 1) (n + 1 - r) (m + 1) hsum, gmap_span]`. Simplify using `only [hg]`. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[hu_def]`. Simplify using `using hM`.

Simplify using `only [hu_def, Fin.cons_succ]`. Conclude with `(Submodule.mem_inf.mp (hvmem i)).1`. Rewrite using `[finrank_span_eq_card hu]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish `hsum' : m + (n + 1 - r + 1) = n + 1` using `by omega show gmap g (Mj k (n + 1) (n + 1 - r + 1)) = M ⊓ H0 k n`. Rewrite using `[Mj_eq_span (n + 1) (n + 1 - r + 1) m hsum', gmap_span]`. Establish `hgv : ∀ i : Fin m, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ ej (n + 1) (n + 1 - r + 1) m hsum' i = v i`. Introduce `i`. Establish `hej : ej (k` using `k) (n + 1) (n + 1 - r + 1) m hsum' i = ej (n + 1) (n + 1 - r) (m + 1) hsum i.succ := by`.

Simplify using `only [ej]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hej, hg i.succ, hu_def, Fin.cons_succ]`. Simplify using `only [hgv]`. Conclude with `hspanv`. Establish `hej : ej (k` using `k) (n + 1) (n + 1 - r) (m + 1) hsum 0 = Pi.single ⟨n + 1 - r, by omega⟩ 1 := by`. Simplify using `only [ej]`.

Use `congr 1`. Rewrite using `[← hej, hg 0, hu_def]`. Both sides reduce to the same expression. Introduce `bb hbb`. Establish `hbb' : n + 1 - r < (bb : ℕ)` using `hbb`.

Establish `hi : (bb : ℕ) - (n + 1 - r + 1) < m` using `by omega`. Set `i : Fin m` to `⟨(bb : ℕ) - (n + 1 - r + 1), hi⟩`. Establish `hej : ej (k` using `k) (n + 1) (n + 1 - r) (m + 1) hsum i.succ = Pi.single bb 1 := by`. Simplify using `only [ej]`. Use `congr 1`.

Use `ext`. Simplify using `[i]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hg i.succ`. Rewrite `h1` using `[hej]`.

Establish `h3 : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single bb 1) 0 = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 bb`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[← h3, h1, hu_def, Fin.cons_succ]`. Conclude with `(Submodule.mem_inf.mp (hvmem i)).2`.
-/
theorem stepMat [Finite k] (n : ℕ) (M : Submodule k (Fin (n + 1) → k)) (hM : e0 k n ∈ M) :
    ∃ (jj : Fin (n + 1)) (g : GL (Fin (n + 1)) k), (jj : ℕ) + finrank k M = n + 1 ∧
      gmap g (Mj k (n + 1) jj) = M ∧ gmap g (Mj k (n + 1) (jj + 1)) = M ⊓ H0 k n ∧
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single jj 1 = e0 k n ∧
      ∀ b : Fin (n + 1), jj < b → (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 b = 0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, r = finrank k M := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hM
    have h5 : (Pi.single (0 : Fin (n + 1)) (1 : k) : Fin (n + 1) → k) 0 = 0 := congrFun hM 0
    simp at h5
  have hrle : r ≤ n + 1 := by
    rw [hr]
    exact (Submodule.finrank_le M).trans (by simp)
  have hH0 : finrank k (H0 k n) = n := by
    rw [lattice_height_zero_eq, finrank_Mj _ _ (by omega)]
    simp
  have hsup : M ⊔ H0 k n = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • e0 k n + (x - x 0 • e0 k n) := by abel
    rw [hx]
    apply Submodule.add_mem_sup (Submodule.smul_mem _ _ hM)
    delta H0 e0
    simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq M (H0 k n)
  rw [hsup, finrank_top, Module.finrank_fin_fun, hH0, ← hr] at hdim
  obtain ⟨m, hm⟩ : ∃ m, m = r - 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Submodule k (Fin (n + 1) → k), P = M ⊓ H0 k n := ⟨_, rfl⟩
  rw [← hP] at hdim
  have hdimMH : finrank k ↥P = m := by omega
  obtain ⟨b⟩ : Nonempty (Basis (Fin m) k ↥P) := ⟨Module.finBasisOfFinrankEq k _ hdimMH⟩
  obtain ⟨v, hv_def⟩ : ∃ v : Fin m → Fin (n + 1) → k, v = fun i => (b i : Fin (n + 1) → k) := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : Fin (m + 1) → Fin (n + 1) → k, u = Fin.cons (e0 k n) v := ⟨_, rfl⟩
  have hvli : LinearIndependent k v := by
    rw [hv_def]
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hspanv : Submodule.span k (Set.range v) = M ⊓ H0 k n := by
    rw [hv_def, ← hP]
    exact span_basis_coe b
  have hvmem : ∀ i, v i ∈ M ⊓ H0 k n := by
    intro i
    rw [hv_def, ← hP]
    exact (b i).2
  have he0 : e0 k n ∉ H0 k n := by
    delta H0 e0
    simp
  have hu : LinearIndependent k u := by
    rw [hu_def, linearIndependent_finCons]
    refine ⟨hvli, ?_⟩
    rw [hspanv]
    intro hmem
    exact he0 (Submodule.mem_inf.mp hmem).2
  have hsum : (m + 1) + (n + 1 - r) = n + 1 := by omega
  obtain ⟨g, hg⟩ := exists_frame (n + 1) (n + 1 - r) (m + 1) hsum u hu
  refine ⟨⟨n + 1 - r, by omega⟩, g, by simp only; omega, ?_, ?_, ?_, ?_⟩
  · show gmap g (Mj k (n + 1) (n + 1 - r)) = M
    rw [Mj_eq_span (n + 1) (n + 1 - r) (m + 1) hsum, gmap_span]
    simp only [hg]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [hu_def]
        simpa using hM
      · simp only [hu_def, Fin.cons_succ]
        exact (Submodule.mem_inf.mp (hvmem i)).1
    · rw [finrank_span_eq_card hu]
      simp
      omega
  · have hsum' : m + (n + 1 - r + 1) = n + 1 := by omega
    show gmap g (Mj k (n + 1) (n + 1 - r + 1)) = M ⊓ H0 k n
    rw [Mj_eq_span (n + 1) (n + 1 - r + 1) m hsum', gmap_span]
    have hgv : ∀ i : Fin m, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ ej (n + 1) (n + 1 - r + 1) m hsum' i = v i := by
      intro i
      have hej : ej (k := k) (n + 1) (n + 1 - r + 1) m hsum' i = ej (n + 1) (n + 1 - r) (m + 1) hsum i.succ := by
        simp only [ej]
        congr 1
        ext
        simp
        omega
      rw [hej, hg i.succ, hu_def, Fin.cons_succ]
    simp only [hgv]
    exact hspanv
  · have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum 0 = Pi.single ⟨n + 1 - r, by omega⟩ 1 := by
      simp only [ej]
      congr 1
    rw [← hej, hg 0, hu_def]
    rfl
  · intro bb hbb
    have hbb' : n + 1 - r < (bb : ℕ) := hbb
    have hi : (bb : ℕ) - (n + 1 - r + 1) < m := by omega
    let i : Fin m := ⟨(bb : ℕ) - (n + 1 - r + 1), hi⟩
    have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum i.succ = Pi.single bb 1 := by
      simp only [ej]
      congr 1
      ext
      simp [i]
      omega
    have h1 := hg i.succ
    rw [hej] at h1
    have h3 : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single bb 1) 0 = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 bb := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← h3, h1, hu_def, Fin.cons_succ]
    exact (Submodule.mem_inf.mp (hvmem i)).2

end PositivityTheory.Rg.Rs.JLatOf

end
