import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.MatRed

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul o z`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 (PadicInt.appr_spec r z)`. Use `⟨(z.appr r) • o, o ⊗ₜ w, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add]`. Use `congr 1`. Rewrite using `[nsmul_eq_mul, nsmul_eq_mul, _root_.mul_one]`. Use `push_cast`. Take the linear combination `hw`.

Consider the case `add x y hx hy`. Take `⟨a, u, ha⟩` from `hx`. Take `⟨b, v, hb⟩` from `hy`. Conclude with `⟨a + b, u + v, by rw [ha, hb, TensorProduct.add_tmul, smul_add]; abel⟩`.
-/
theorem approx {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ) (x : M ⊗[ℤ] ℤ_[p]) :
    ∃ (b : M) (y : M ⊗[ℤ] ℤ_[p]), x = b ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul o z =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec r z)
    refine ⟨(z.appr r) • o, o ⊗ₜ w, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    congr 1
    rw [nsmul_eq_mul, nsmul_eq_mul, _root_.mul_one]
    push_cast
    linear_combination hw
  | add x y hx hy =>
    obtain ⟨a, u, ha⟩ := hx
    obtain ⟨b, v, hb⟩ := hy
    exact ⟨a + b, u + v, by rw [ha, hb, TensorProduct.add_tmul, smul_add]; abel⟩

/- English proof (translation)
Set `bs` to `Module.Free.chooseBasis ℤ M`. Establish `hd : ∀ i, ((p ^ r : ℕ) : ℤ) ∣ bs.repr u i`. Introduce `i`. Set `φ : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p]` to `(TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (bs.coord i) LinearMap.id`. Establish `h1 : φ (u ⊗ₜ (1 : ℤ_[p])) = ((bs.repr u i : ℤ) : ℤ_[p])` using `by show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (bs.coord i) LinearMap.id (u ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _`.

Rewrite using `[TensorProduct.map_tmul, TensorProduct.lid_tmul]`. Simplify using `[zsmul_eq_mul]`. Rewrite `h1` using `[h, map_nsmul]`. Establish `h2` using `congrArg (PadicInt.toZModPow (p := p) r) h1`. Rewrite `h2` using `[map_nsmul, map_intCast]`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2, nsmul_eq_mul]`. Simplify using the standard rewrite rules. Use `choose k hk using hd`. Use `⟨∑ i, k i • bs i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← bs.sum_repr u]`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hk i, mul_smul, natCast_zsmul]`.
-/
theorem dvd_of_tmul {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (r : ℕ) (u : M) (z : M ⊗[ℤ] ℤ_[p]) (h : u ⊗ₜ (1 : ℤ_[p]) = (p ^ r) • z) :
    ∃ v : M, u = (p ^ r) • v := by
  let bs := Module.Free.chooseBasis ℤ M
  have hd : ∀ i, ((p ^ r : ℕ) : ℤ) ∣ bs.repr u i := by
    intro i
    let φ : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p] :=
      (TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (bs.coord i) LinearMap.id
    have h1 : φ (u ⊗ₜ (1 : ℤ_[p])) = ((bs.repr u i : ℤ) : ℤ_[p]) := by
      show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (bs.coord i) LinearMap.id (u ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
      simp [zsmul_eq_mul]
    rw [h, map_nsmul] at h1
    have h2 := congrArg (PadicInt.toZModPow (p := p) r) h1
    rw [map_nsmul, map_intCast] at h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2, nsmul_eq_mul]
    simp
  choose k hk using hd
  refine ⟨∑ i, k i • bs i, ?_⟩
  conv_lhs => rw [← bs.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk i, mul_smul, natCast_zsmul]

/- English proof (translation)
Establish `h` using `Submodule.mem_map_of_mem (f := f) hx`. Rewrite `h` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top h`.
-/
theorem mem_smul_top_map {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (f : X →ₗ[R] Y) {x : X} (hx : x ∈ I • (⊤ : Submodule R X)) :
    f x ∈ I • (⊤ : Submodule R Y) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

/- English proof (translation)
Introduce `p _ D w0 r _ hp`. Use `haveI := D.freeO`. Use `haveI := D.finO`. Take `⟨e⟩` from `D.splitP`. Establish `hpr : (p : 𝓞 D.F) ^ r ∈ w0 ^ r` using `Ideal.pow_mem_pow hp r`.

Establish `hA : ((p ^ r : ℕ) : 𝓞 D.F ⧸ w0 ^ r) = 0`. Establish `h` using `Ideal.Quotient.eq_zero_iff_mem.2 hpr`. Simplify using `using h`. Set `ψ₀ : ℤ_[p] →+* 𝓞 D.F ⧸ w0 ^ r` to `(ZMod.castHom (ringChar.dvd hA) (𝓞 D.F ⧸ w0 ^ r)).comp (PadicInt.toZModPow r)`. Set `ψ : 𝓞 D.F ⊗[ℤ] ℤ_[p] →ₐ[𝓞 D.F] 𝓞 D.F ⧸ w0 ^ r` to `Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (𝓞 D.F) (w0 ^ r)) ψ₀.toIntAlgHom (fun _ _ => Commute.all _ _)`.

Establish `hψ : ∀ c, ψ (c ⊗ₜ (1 : ℤ_[p])) = Ideal.Quotient.mk _ c`. Introduce `c`. Simplify using `[ψ, Algebra.TensorProduct.lift_tmul]`. Establish `hψk : ∀ y, ψ y = 0 → y ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))`. Introduce `y hy`.

Take `⟨c, z, rfl⟩` from `approx r y`. Rewrite `hy` using `[map_add, map_nsmul, hψ, nsmul_eq_mul, hA, zero_mul, add_zero]`. Establish `hc : c ∈ w0 ^ r` using `Ideal.Quotient.eq_zero_iff_mem.1 hy`. Establish `h1 : c ⊗ₜ[ℤ] (1 : ℤ_[p]) = c • (1 : 𝓞 D.F ⊗[ℤ] ℤ_[p])`. Rewrite using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`.

Establish `h2 : (p ^ r) • z = ((p : 𝓞 D.F) ^ r) • z`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Rewrite using `[h1, h2]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem_smul hc trivial) (Submodule.smul_mem_smul hpr trivial)`. Set `incl : D.O →ₐ[𝓞 D.F] D.O ⊗[ℤ] ℤ_[p]` to `Algebra.TensorProduct.includeLeft`.

Establish `hincl : ∀ b, incl b = b ⊗ₜ (1 : ℤ_[p])` using `fun b => rfl`. Use `⟨ψ.mapMatrix.comp (e.toAlgHom.comp incl), ?_, ?_⟩` and prove the remaining obligations. Introduce `N choose c hc using fun i j => Ideal.Quotient.mk_surjective (N i j)`. Take `⟨b, y, hby⟩` from `approx (M := D.O) r (e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])))`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Establish `hb : incl b = e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])) - (p ^ r) • y`. Rewrite using `[hby, hincl]`. Normalize the expressions using the abelian group laws. Use `show ψ.mapMatrix (e (incl b)) = N`. Rewrite using `[hb, map_sub, map_sub, map_nsmul, map_nsmul, e.apply_symm_apply]`.

Use extensionality with `i j`. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, nsmul_eq_mul, hA, zero_mul, sub_zero]`. Simplify using `[AlgHom.mapMatrix_apply, hψ, hc]`. Introduce `b hb`. Establish `hb' : ∀ i j, ψ (e (incl b) i j) = 0` using `fun i j => by`.

Establish `h` using `congrFun (congrFun hb i) j`. Simplify `h` using `[AlgHom.mapMatrix_apply]`. Establish `hM : e (incl b) ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])))`. Rewrite using `[Matrix.matrix_eq_sum_single (e (incl b))]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `mem_smul_top_map _ (Matrix.singleLinearMap (𝓞 D.F) i j) (hψk _ (hb' i j))`. Establish `hO : incl b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]))`. Establish `h` using `mem_smul_top_map _ e.symm.toLinearEquiv.toLinearMap hM`. Simplify using `using h`. Establish `claim : ∀ x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])), ∃ b' ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O), ∃ z : D.O ⊗[ℤ] ℤ_[p], x = b' ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • z`.

Introduce `x hx`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `c hc x _`. Take `⟨bx, y, rfl⟩` from `approx r x`. Use `⟨c • bx, Submodule.smul_mem_smul hc trivial, c • y, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add, TensorProduct.smul_tmul', smul_comm]`. Introduce and unpack `x y ⟨a, ha, u, rfl⟩ ⟨a', ha', v, rfl⟩`. Conclude with `⟨a + a', add_mem ha ha', u + v, by rw [TensorProduct.add_tmul, smul_add]; abel⟩`. Take `⟨b', hb'', z, hz⟩` from `claim _ hO`. Rewrite `hz` using `[hincl]`.

Establish `h3 : (b - b') ⊗ₜ[ℤ] (1 : ℤ_[p]) = (p ^ r) • z`. Rewrite using `[TensorProduct.sub_tmul, hz]`. Normalize the expressions using the abelian group laws. Take `⟨v, hv⟩` from `dvd_of_tmul r (b - b') z h3`. Establish `h4 : b = b' + ((p : 𝓞 D.F) ^ r) • v`.

Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hv]`. Normalize the expressions using the abelian group laws. Rewrite using `[h4]`. Conclude with `add_mem hb'' (Submodule.smul_mem_smul hpr trivial)`.
-/
theorem exists_matRed : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  intro p _ D w0 r _ hp
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e⟩ := D.splitP
  have hpr : (p : 𝓞 D.F) ^ r ∈ w0 ^ r := Ideal.pow_mem_pow hp r
  have hA : ((p ^ r : ℕ) : 𝓞 D.F ⧸ w0 ^ r) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hpr
    simpa using h
  let ψ₀ : ℤ_[p] →+* 𝓞 D.F ⧸ w0 ^ r :=
    (ZMod.castHom (ringChar.dvd hA) (𝓞 D.F ⧸ w0 ^ r)).comp (PadicInt.toZModPow r)
  let ψ : 𝓞 D.F ⊗[ℤ] ℤ_[p] →ₐ[𝓞 D.F] 𝓞 D.F ⧸ w0 ^ r :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (𝓞 D.F) (w0 ^ r)) ψ₀.toIntAlgHom
      (fun _ _ => Commute.all _ _)
  have hψ : ∀ c, ψ (c ⊗ₜ (1 : ℤ_[p])) = Ideal.Quotient.mk _ c := by
    intro c; simp [ψ, Algebra.TensorProduct.lift_tmul]
  have hψk : ∀ y, ψ y = 0 → y ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    intro y hy
    obtain ⟨c, z, rfl⟩ := approx r y
    rw [map_add, map_nsmul, hψ, nsmul_eq_mul, hA, zero_mul, add_zero] at hy
    have hc : c ∈ w0 ^ r := Ideal.Quotient.eq_zero_iff_mem.1 hy
    have h1 : c ⊗ₜ[ℤ] (1 : ℤ_[p]) = c • (1 : 𝓞 D.F ⊗[ℤ] ℤ_[p]) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (p ^ r) • z = ((p : 𝓞 D.F) ^ r) • z := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc trivial) (Submodule.smul_mem_smul hpr trivial)
  let incl : D.O →ₐ[𝓞 D.F] D.O ⊗[ℤ] ℤ_[p] := Algebra.TensorProduct.includeLeft
  have hincl : ∀ b, incl b = b ⊗ₜ (1 : ℤ_[p]) := fun b => rfl
  refine ⟨ψ.mapMatrix.comp (e.toAlgHom.comp incl), ?_, ?_⟩
  · intro N
    choose c hc using fun i j => Ideal.Quotient.mk_surjective (N i j)
    obtain ⟨b, y, hby⟩ := approx (M := D.O) r (e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])))
    refine ⟨b, ?_⟩
    have hb : incl b = e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])) - (p ^ r) • y := by
      rw [hby, hincl]; abel
    show ψ.mapMatrix (e (incl b)) = N
    rw [hb, map_sub, map_sub, map_nsmul, map_nsmul, e.apply_symm_apply]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, nsmul_eq_mul, hA, zero_mul, sub_zero]
    simp [AlgHom.mapMatrix_apply, hψ, hc]
  · intro b hb
    have hb' : ∀ i j, ψ (e (incl b) i j) = 0 := fun i j => by
      have h := congrFun (congrFun hb i) j
      simpa [AlgHom.mapMatrix_apply] using h
    have hM : e (incl b) ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]))) := by
      rw [Matrix.matrix_eq_sum_single (e (incl b))]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      exact mem_smul_top_map _ (Matrix.singleLinearMap (𝓞 D.F) i j) (hψk _ (hb' i j))
    have hO : incl b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])) := by
      have h := mem_smul_top_map _ e.symm.toLinearEquiv.toLinearMap hM
      simpa using h
    have claim : ∀ x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])),
        ∃ b' ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O), ∃ z : D.O ⊗[ℤ] ℤ_[p],
          x = b' ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • z := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro c hc x _
        obtain ⟨bx, y, rfl⟩ := approx r x
        refine ⟨c • bx, Submodule.smul_mem_smul hc trivial, c • y, ?_⟩
        rw [smul_add, TensorProduct.smul_tmul', smul_comm]
      · rintro x y ⟨a, ha, u, rfl⟩ ⟨a', ha', v, rfl⟩
        exact ⟨a + a', add_mem ha ha', u + v, by rw [TensorProduct.add_tmul, smul_add]; abel⟩
    obtain ⟨b', hb'', z, hz⟩ := claim _ hO
    rw [hincl] at hz
    have h3 : (b - b') ⊗ₜ[ℤ] (1 : ℤ_[p]) = (p ^ r) • z := by
      rw [TensorProduct.sub_tmul, hz]; abel
    obtain ⟨v, hv⟩ := dvd_of_tmul r (b - b') z h3
    have h4 : b = b' + ((p : 𝓞 D.F) ^ r) • v := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hv]; abel
    rw [h4]
    exact add_mem hb'' (Submodule.smul_mem_smul hpr trivial)

end GlobalTheory.UPel.HT.MatRed
