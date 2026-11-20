import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.FinSumFinEquivSymmEq

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir PositivityTheory.RgUd.Form

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[TrM.colEl_zero] col_add x y v := by rw [TrM.colEl_add, map_mul, Module.End.mul_apply] conj g x v := by show π (blkAt k (m + 1) N h' g) (π (colEl k m N h x) v) = π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π (blkAt k (m + 1) N h' g) v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, TrM.blkAt_mul_colEl m N h h', map_mul, Module.End.mul_apply]`. Use `smooth_col v := (hπ v).preimage (TrM.continuous_colEl m N h)`. Use `smooth_gl v := (hπ v).preimage (TrM.continuous_blkAt (m + 1) N h')`.
-/
theorem setup_tr {m N : ℕ} (h : m + 2 ≤ N) (h' : m + 1 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) :
    Setup (fun x => π (colEl k m N h x)) (π.comp (blkAt k (m + 1) N h')) where
  col_zero v := by simp [TrM.colEl_zero]
  col_add x y v := by rw [TrM.colEl_add, map_mul, Module.End.mul_apply]
  conj g x v := by
    show π (blkAt k (m + 1) N h' g) (π (colEl k m N h x) v) =
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π (blkAt k (m + 1) N h' g) v)
    rw [← Module.End.mul_apply, ← map_mul, TrM.blkAt_mul_colEl m N h h', map_mul, Module.End.mul_apply]
  smooth_col v := (hπ v).preimage (TrM.continuous_colEl m N h)
  smooth_gl v := (hπ v).preimage (TrM.continuous_blkAt (m + 1) N h')

/- English proof (translation)
Introduce `ψ hψ hψ1 m N h V _ _ π hπ s B B' C A₀ hL hA₀ hD hC hCK hCM hle`. Establish `h' : m + 1 ≤ N` using `by omega`. Take `⟨hBpsd, _, hBM⟩` from `hL`. Establish `hBcol : ∀ x v w, B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w`. Introduce `x v w`.

Establish `hn : ((nabs k (GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x))) ^ s : ℝ) : ℂ) = 1`. Rewrite using `[TrM.det_unip_GL]`. Simplify using `[nabs]`. Conclude with `(hBM _ (MirU_le_Mir k (m + 1) (MonoidHom.mem_range.2 ⟨_, rfl⟩)) v w).trans (by rw [hn, one_mul])`. Establish `hBgl : ∀ g v w, B ((π.comp (blkAt k (m + 1) N h')) g v) ((π.comp (blkAt k (m + 1) N h')) g w) = ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w`.

Introduce `g v w`. Use `hBM (glEmb k (m + 1) g) (glEmb_mem_Mir k (m + 1) g) v w` as an intermediate fact. Rewrite `this` using `[TrM.det_glEmb_GL]`. Rewrite using `[MonoidHom.comp_apply, TrM.blkAt_glEmb (m + 1) N h' h]`. Conclude with `this`.

Establish `hCcol : ∀ x v w, C (π (colEl k m N h x) v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w`. Introduce `x v w`. Establish `hmem : π (colEl k m N h x) v - ((lvlChar k ψ N (m + 1) ⟨colEl k m N h x, TrM.colEl_mem m N h x⟩ : ℂˣ) : ℂ) • v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1))` using `Submodule.subset_span ⟨⟨_, TrM.colEl_mem m N h x⟩, v, rfl⟩`. Establish `h0` using `hCK _ hmem w`. Rewrite `h0` using `[map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, smul_eq_mul, TrM.lvlChar_colEl]`.

Rewrite using `[h0]`. Simplify using `[xz]`. Take `⟨I, hIpsd, hIcol, hIgl, hIle, hID, hIA, hIY⟩` from `H ψ hψ hψ1 m V (fun x => π (colEl k m N h x)) (π.comp (blkAt k (m + 1) N h')) (setup_tr h h' π hπ) s B B' C A₀ hA₀ hBpsd hBcol hBgl hD hC hCcol hCM hle`. Use `⟨I, ⟨hIpsd, ?_, ?_⟩, hIle, hID, hIA⟩` and prove the remaining obligations. Introduce `v hv w`.

Conclude with `hIY (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) (fun g y hy => TrM.twKer_blkAt ψ π m h' g y hy) (fun y hy w => hCK y (TrM.twKer_le_succ ψ π m hy) w) v hv w`. Introduce `p hp v w`. Take `⟨x, g, rfl⟩` from `TrM.mir_decomp (m + 1) p hp`. Establish `e : ∀ u, π (blkAt k (m + 1 + 1) N h (unip k (m + 1) (Multiplicative.ofAdd x) * glEmb k (m + 1) g)) u = π (colEl k m N h x) (π (blkAt k (m + 1) N h' g) u)`. Introduce `u`.

Rewrite using `[map_mul, map_mul, Module.End.mul_apply, ← TrM.blkAt_glEmb (m + 1) N h' h]`. Both sides reduce to the same expression. Rewrite using `[e, e, TrM.det_unip_mul_glEmb]`. Conclude with `(hIcol x _ _).trans (hIgl g v w)`.
-/
theorem uLift_of_abs (H : @AbsLift k _ _ _ _) : PositivityTheory.RgUd.Form.U.ULift k := by
  intro ψ hψ hψ1 m N h V _ _ π hπ s B B' C A₀ hL hA₀ hD hC hCK hCM hle
  have h' : m + 1 ≤ N := by omega
  obtain ⟨hBpsd, _, hBM⟩ := hL
  have hBcol : ∀ x v w, B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
    intro x v w
    have hn : ((nabs k (GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x))) ^ s : ℝ) : ℂ) = 1 := by
      rw [TrM.det_unip_GL]
      simp [nabs]
    exact (hBM _ (MirU_le_Mir k (m + 1) (MonoidHom.mem_range.2 ⟨_, rfl⟩)) v w).trans (by rw [hn, one_mul])
  have hBgl : ∀ g v w, B ((π.comp (blkAt k (m + 1) N h')) g v) ((π.comp (blkAt k (m + 1) N h')) g w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w := by
    intro g v w
    have := hBM (glEmb k (m + 1) g) (glEmb_mem_Mir k (m + 1) g) v w
    rw [TrM.det_glEmb_GL] at this
    rw [MonoidHom.comp_apply, TrM.blkAt_glEmb (m + 1) N h' h]
    exact this
  have hCcol : ∀ x v w, C (π (colEl k m N h x) v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w := by
    intro x v w
    have hmem : π (colEl k m N h x) v -
        ((lvlChar k ψ N (m + 1) ⟨colEl k m N h x, TrM.colEl_mem m N h x⟩ : ℂˣ) : ℂ) • v ∈
          twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) :=
      Submodule.subset_span ⟨⟨_, TrM.colEl_mem m N h x⟩, v, rfl⟩
    have h0 := hCK _ hmem w
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, smul_eq_mul,
      TrM.lvlChar_colEl] at h0
    rw [h0]
    simp [xz]
  obtain ⟨I, hIpsd, hIcol, hIgl, hIle, hID, hIA, hIY⟩ := H ψ hψ hψ1 m V (fun x => π (colEl k m N h x))
    (π.comp (blkAt k (m + 1) N h')) (setup_tr h h' π hπ) s B B' C A₀ hA₀ hBpsd hBcol hBgl hD hC hCcol hCM hle
  refine ⟨I, ⟨hIpsd, ?_, ?_⟩, hIle, hID, hIA⟩
  · intro v hv w
    exact hIY (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)))
      (fun g y hy => TrM.twKer_blkAt ψ π m h' g y hy) (fun y hy w => hCK y (TrM.twKer_le_succ ψ π m hy) w) v hv w
  · intro p hp v w
    obtain ⟨x, g, rfl⟩ := TrM.mir_decomp (m + 1) p hp
    have e : ∀ u, π (blkAt k (m + 1 + 1) N h (unip k (m + 1) (Multiplicative.ofAdd x) * glEmb k (m + 1) g)) u =
        π (colEl k m N h x) (π (blkAt k (m + 1) N h' g) u) := by
      intro u
      rw [map_mul, map_mul, Module.End.mul_apply, ← TrM.blkAt_glEmb (m + 1) N h' h]
      rfl
    rw [e, e, TrM.det_unip_mul_glEmb]
    exact (hIcol x _ _).trans (hIgl g v w)

end PositivityTheory.RgUd.Form.U.Lift2
