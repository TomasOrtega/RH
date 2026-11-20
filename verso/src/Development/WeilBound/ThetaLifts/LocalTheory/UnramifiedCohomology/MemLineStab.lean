import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace

noncomputable section

namespace PositivityTheory.ThKG.Loc.Iwa

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.1 hx`. Establish `hj' : x j ≠ 0` using `hj`. Set `p₀ : Fin n → K` to `Pi.single j (x j)⁻¹`. Establish `hp₀ : p₀ ⬝ᵥ x = 1` using `by simp [p₀, hj']`. Set `p : Fin n → K` to `p₀ - (p₀ ⬝ᵥ y) • φ`.

Establish `hpx : p ⬝ᵥ x = 1` using `by simp [p, sub_dotProduct, smul_dotProduct, h0, hp₀]`. Establish `hpy : p ⬝ᵥ y = 0` using `by simp [p, sub_dotProduct, smul_dotProduct, h1]`. Set `f : (Fin n → K) →ₗ[K] K × K` to `((dotProductBilin K K p).prod (dotProductBilin K K φ))`. Establish `hf : ∀ z, f z = (p ⬝ᵥ z, φ ⬝ᵥ z)` using `fun _ => rfl`. Establish `hs : LinearMap.range f = ⊤` using `LinearMap.range_eq_top.2 fun ⟨a, b⟩ => ⟨a • x + b • y, by`.

Simplify using `[hf, dotProduct_add, dotProduct_smul, hpx, hpy, h0, h1]⟩`. Establish `hr` using `LinearMap.finrank_range_add_finrank_ker f`. Rewrite `hr` using `[hs]`. Simplify using `only [finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at hr`. Set `b` to `Module.finBasis K (LinearMap.ker f)`.

Set `P : (Fin n → K) →ₗ[K] LinearMap.ker f` to `LinearMap.codRestrict _ (LinearMap.id - (dotProductBilin K K p).smulRight x - (dotProductBilin K K φ).smulRight y) fun z => by`. Simplify using `[LinearMap.mem_ker, hf, dotProduct_sub, dotProduct_smul, hpx, hpy, h0, h1]`. Use `⟨_, Matrix.of fun r k => (b k).1 r, Matrix.of fun k c => b.repr (P (Pi.single c 1)) k, p, by omega, hpx, ?_⟩` and prove the remaining obligations. Use extensionality with `r c`. Establish `e` using `congrArg (fun z : LinearMap.ker f => z.1 r) (b.sum_repr (P (Pi.single c 1)))`.

Establish `e2 : (P (Pi.single c 1)).1 r = (Pi.single c 1 : Fin n → K) r - p c * x r - φ c * y r`. Simplify using `[P]`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at e`. Simplify using `only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, mul_comm ((b _).1 r), e, e2, Matrix.one_apply, Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_frame {K : Type} [Field K] {n : ℕ} (x y : Fin n → K) (φ : Fin n → K) (hx : x ≠ 0) (h0 : φ ⬝ᵥ x = 0)
    (h1 : φ ⬝ᵥ y = 1) : ∃ (m : ℕ) (i : Matrix (Fin n) (Fin m) K) (q : Matrix (Fin m) (Fin n) K) (p : Fin n → K),
      n = m + 2 ∧ p ⬝ᵥ x = 1 ∧ Matrix.vecMulVec x p + i * q + Matrix.vecMulVec y φ = 1 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have hj' : x j ≠ 0 := hj
  let p₀ : Fin n → K := Pi.single j (x j)⁻¹
  have hp₀ : p₀ ⬝ᵥ x = 1 := by simp [p₀, hj']
  let p : Fin n → K := p₀ - (p₀ ⬝ᵥ y) • φ
  have hpx : p ⬝ᵥ x = 1 := by simp [p, sub_dotProduct, smul_dotProduct, h0, hp₀]
  have hpy : p ⬝ᵥ y = 0 := by simp [p, sub_dotProduct, smul_dotProduct, h1]
  let f : (Fin n → K) →ₗ[K] K × K := ((dotProductBilin K K p).prod (dotProductBilin K K φ))
  have hf : ∀ z, f z = (p ⬝ᵥ z, φ ⬝ᵥ z) := fun _ => rfl
  have hs : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 fun ⟨a, b⟩ => ⟨a • x + b • y, by
    simp [hf, dotProduct_add, dotProduct_smul, hpx, hpy, h0, h1]⟩
  have hr := LinearMap.finrank_range_add_finrank_ker f
  rw [hs] at hr
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at hr
  let b := Module.finBasis K (LinearMap.ker f)
  let P : (Fin n → K) →ₗ[K] LinearMap.ker f := LinearMap.codRestrict _
    (LinearMap.id - (dotProductBilin K K p).smulRight x - (dotProductBilin K K φ).smulRight y) fun z => by
      simp [LinearMap.mem_ker, hf, dotProduct_sub, dotProduct_smul, hpx, hpy, h0, h1]
  refine ⟨_, Matrix.of fun r k => (b k).1 r, Matrix.of fun k c => b.repr (P (Pi.single c 1)) k, p, by omega, hpx, ?_⟩
  ext r c
  have e := congrArg (fun z : LinearMap.ker f => z.1 r) (b.sum_repr (P (Pi.single c 1)))
  have e2 : (P (Pi.single c 1)).1 r = (Pi.single c 1 : Fin n → K) r - p c * x r - φ c * y r := by
    simp [P]
  simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at e
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, mul_comm ((b _).1 r), e, e2,
    Matrix.one_apply, Pi.single_apply]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def lineStab (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (GAd σ J) where
  carrier := {g | ∃ t : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 *ᵥ (fun i => inclR (AF F) (x i)) = t.1 • fun i => inclR (AF F) (x i)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨t * s, by rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, hs, smul_smul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have := congrArg (fun z => (s⁻¹).1 • ((matHom _ σ J a⁻¹).1 *ᵥ z)) hs
    simp only [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, one_smul] at this
    rw [map_inv]
    exact this.symm

/- English proof (translation)
Use `⟨Matrix.GeneralLinearGroup.det β, funext fun i => ?_⟩` and prove the remaining obligations. Establish `: (matHom _ σ J g).1 i ⬝ᵥ (fun j => inclR (AF F) (x j)) = ∑ k : Fin 1, inclR (AF F) (x i) * β.1 k 0` using `congrFun (congrFun h i) 0`. Rewrite `this` using `[Fin.sum_univ_one]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, mul_comm]`. Conclude with `this`.
-/
theorem mem_lineStab {x : Fin n → E} {g : GAd σ J} (β : GL (Fin 1) (AF F ⊗[F] E))
    (h : (matHom _ σ J g).1 * (Matrix.replicateCol (Fin 1) x).map (inclR (AF F)) =
      (Matrix.replicateCol (Fin 1) x).map (inclR (AF F)) * β.1) : g ∈ lineStab σ J x := by
  refine ⟨Matrix.GeneralLinearGroup.det β, funext fun i => ?_⟩
  have : (matHom _ σ J g).1 i ⬝ᵥ (fun j => inclR (AF F) (x j)) = ∑ k : Fin 1, inclR (AF F) (x i) * β.1 k 0 :=
    congrFun (congrFun h i) 0
  rw [Fin.sum_univ_one] at this
  rw [Pi.smul_apply, smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, mul_comm]
  exact this

/- English proof (translation)
Establish `hφ : (fun i => σ (x i)) ᵥ* J ≠ 0` using `fun h => hx (funext fun i => σ.injective (by`. Use `Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h` as an intermediate fact. Simplify using `using congrFun this i))`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hφ`. Establish `hj' : ((fun i => σ (x i)) ᵥ* J) j ≠ 0` using `hj`.

Take `⟨m, i, q, p, hn, hp, hsum⟩` from `exists_frame x (Pi.single j (((fun i => σ (x i)) ᵥ* J) j)⁻¹) _ hx h0 (by simp [hj'])`. Use `set y : Fin n → E := Pi.single j (((fun i => σ (x i)) ᵥ* J) j)⁻¹ with hy`. Establish `hp' : Matrix.replicateRow (Fin 1) p * Matrix.replicateCol (Fin 1) x = 1`. Use extensionality with `a b`. Rewrite using `[Subsingleton.elim a b, Matrix.one_apply_eq, ← hp]`.

Both sides reduce to the same expression. Establish `hrow : ((Matrix.replicateCol (Fin 1) x).map σ)ᵀ * J = Matrix.replicateRow (Fin 1) ((fun i => σ (x i)) ᵥ* J)`. Use extensionality with `a b`. Both sides reduce to the same expression. Break down `hsi with ⟨⟨τ⟩⟩ | ⟨w, hw⟩` into its components or cases.

Take `⟨B, lv, hB⟩` from `GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ (e := Matrix.replicateCol (Fin 1) x) (e' := Matrix.replicateCol (Fin 1) y) (i := i) (p := Matrix.replicateRow (Fin 1) p) (q := q) (Fintype.equivOfCardEq (by simp; omega)) (by rw [hrow, ← hsum]; ext a b; simp [Matrix …`. Express the relevant statement in the definitionally equal form `_ ⬝ᵥ y = 1`. Simplify using `[hy, hj'])`. Use `GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular hσ hJ τ L hL ((lineStab σ J x).comap (emb σ J v)) B lv (fun g hg => ?_) g` and prove the remaining obligations. Take `⟨⟨a, ha⟩, a', ha'⟩` from `hB g hg`.

Establish `hpA : (Matrix.replicateRow (Fin 1) p).map (inclR (F` using `F) (AF F)) * (Matrix.replicateCol (Fin 1) x).map (inclR (F := F) (AF F)) = 1 := by`. Rewrite using `[← Matrix.map_mul, hp', Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h1` using `GlobalTheory.Core.Rk.IwFlagSplit.emb_keeps hσ τ g hpA rfl ha ha'`. Rewrite using `[Subgroup.mem_comap]`. Generalize the expression as in `emb σ J v g = z at h1 ⊢`.

Use `set X := (Matrix.replicateCol (Fin 1) x).map (inclR (F := F) (AF F))`. Use `set P := (Matrix.replicateRow (Fin 1) p).map (inclR (F := F) (AF F))`. Establish `h2 : (P * ((matHom _ σ J z⁻¹).1 * X)) * (P * ((matHom _ σ J z).1 * X)) = 1`. Rewrite using `[Matrix.mul_assoc P, Matrix.mul_assoc (matHom _ σ J z⁻¹).1, ← h1, ← Matrix.mul_assoc (matHom _ σ J z⁻¹).1, map_inv, Units.inv_mul, Matrix.one_mul, hpA]`. Conclude with `mem_lineStab ⟨_, _, mul_eq_one_comm.1 h2, h2⟩ h1`.

Take `⟨q', k, ⟨β, hβ⟩, hk, e⟩` from `GlobalTheory.InertIwasawaIso.exists_of_inert hσ hc hJ hw hv hL hp' (by`. Express the relevant statement in the definitionally equal form `((Matrix.replicateCol (Fin 1) x).map σ)ᵀ * J * _ = 0`. Rewrite using `[hrow]`. Use extensionality with `a b`. Conclude with `h0) g`.

Conclude with `⟨q', k, mem_lineStab β hβ, hk, e⟩`.
-/
theorem core (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v)
    (hsi : Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w, Formalism.UG.IsInertAt F E v w) (hL : IsSelfDualAt σ J L v) {x : Fin n → E}
    (hx : x ≠ 0) (h0 : ((fun i => σ (x i)) ᵥ* J) ⬝ᵥ x = 0) (g : GLoc σ J v) :
    ∃ q k : GLoc σ J v, emb σ J v q ∈ lineStab σ J x ∧ k ∈ stabLoc σ J L v ∧ g = q * k := by
  classical
  have hφ : (fun i => σ (x i)) ᵥ* J ≠ 0 := fun h => hx (funext fun i => σ.injective (by
    have := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h
    simpa using congrFun this i))
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hφ
  have hj' : ((fun i => σ (x i)) ᵥ* J) j ≠ 0 := hj
  obtain ⟨m, i, q, p, hn, hp, hsum⟩ := exists_frame x (Pi.single j (((fun i => σ (x i)) ᵥ* J) j)⁻¹) _ hx h0 (by simp [hj'])
  set y : Fin n → E := Pi.single j (((fun i => σ (x i)) ᵥ* J) j)⁻¹ with hy
  have hp' : Matrix.replicateRow (Fin 1) p * Matrix.replicateCol (Fin 1) x = 1 := by
    ext a b; rw [Subsingleton.elim a b, Matrix.one_apply_eq, ← hp]; rfl
  have hrow : ((Matrix.replicateCol (Fin 1) x).map σ)ᵀ * J = Matrix.replicateRow (Fin 1) ((fun i => σ (x i)) ᵥ* J) := by
    ext a b; rfl
  rcases hsi with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ (e := Matrix.replicateCol (Fin 1) x)
      (e' := Matrix.replicateCol (Fin 1) y) (i := i) (p := Matrix.replicateRow (Fin 1) p) (q := q)
      (Fintype.equivOfCardEq (by simp; omega))
      (by rw [hrow, ← hsum]; ext a b; simp [Matrix.mul_apply, Matrix.vecMulVec_apply])
      (by rw [hrow]; ext a b; rw [Subsingleton.elim a b, Matrix.one_apply_eq]
          change _ ⬝ᵥ y = 1
          simp [hy, hj'])
    refine GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular hσ hJ τ L hL ((lineStab σ J x).comap (emb σ J v)) B lv
      (fun g hg => ?_) g
    obtain ⟨⟨a, ha⟩, a', ha'⟩ := hB g hg
    have hpA : (Matrix.replicateRow (Fin 1) p).map (inclR (F := F) (AF F)) * (Matrix.replicateCol (Fin 1) x).map (inclR (F := F) (AF F)) = 1 := by
      rw [← Matrix.map_mul, hp', Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 := GlobalTheory.Core.Rk.IwFlagSplit.emb_keeps hσ τ g hpA rfl ha ha'
    rw [Subgroup.mem_comap]
    generalize emb σ J v g = z at h1 ⊢
    set X := (Matrix.replicateCol (Fin 1) x).map (inclR (F := F) (AF F))
    set P := (Matrix.replicateRow (Fin 1) p).map (inclR (F := F) (AF F))
    have h2 : (P * ((matHom _ σ J z⁻¹).1 * X)) * (P * ((matHom _ σ J z).1 * X)) = 1 := by
      rw [Matrix.mul_assoc P, Matrix.mul_assoc (matHom _ σ J z⁻¹).1, ← h1, ← Matrix.mul_assoc (matHom _ σ J z⁻¹).1,
        map_inv, Units.inv_mul, Matrix.one_mul, hpA]
    exact mem_lineStab ⟨_, _, mul_eq_one_comm.1 h2, h2⟩ h1
  · obtain ⟨q', k, ⟨β, hβ⟩, hk, e⟩ := GlobalTheory.InertIwasawaIso.exists_of_inert hσ hc hJ hw hv hL hp'
      (by
        change ((Matrix.replicateCol (Fin 1) x).map σ)ᵀ * J * _ = 0
        rw [hrow]; ext a b; exact h0) g
    exact ⟨q', k, mem_lineStab β hβ, hk, e⟩

end PositivityTheory.ThKG.Loc.Iwa

end
