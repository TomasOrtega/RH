import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisSo

/- English proof (translation)
Introduce `hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ`. Establish `hL : (adStd F).GoodL` using `hS F`. Take `⟨-, -, -, -, hk, hd⟩` from `hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ`. Establish `hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ)`. Establish `h` using `Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F])) (Continuous.matrix_det continuous_id)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Establish `hprj : Continuous (prj A ν ι)` using `continuous_snd.comp continuous_subtype_val`.

Establish `hfst : Continuous fun x : cover A ν ι => x.1.1` using `continuous_fst.comp continuous_subtype_val`. Establish `hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g`. Introduce `p g`. Simplify using `only [ld, map_mul]`. Conclude with `hL.lgmul _ _`.

Establish `hK : ∀ k ∈ cK α j, ld k = 0`. Introduce `k hk'`. Take `⟨κ, hκ, he⟩` from `hk'.2`. Establish `hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ`. Rewrite using `[← he]`.

Simplify using `[MulAut.conj_apply, map_mul, map_inv, mul_comm]`. Use `hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ` as an intermediate fact. Rewrite `this` using `[hd]`. Simplify using `only [ld, hdk]`. Conclude with `this`.

Use `⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `p _ q _`. Simplify using `[c0]`. Introduce `p _`. Conclude with `Circle.norm_coe _`.

Introduce `γ hγ _`. Take `⟨⟨x, hx⟩, -⟩` from `hγ`. Use `hG.toGoodL.χi x` as an intermediate fact. Simplify using `only [c0]`. Establish `hx' : Units.map A.i.toMonoidHom x = γ.1.1` using `hx`.

Rewrite using `[← hx', this]`. Simplify using the standard rewrite rules. Conclude with `(continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn`. Introduce `p _ g`. Conclude with `hadd p g`.

Introduce `g k hk'`. Rewrite using `[hadd, hK k hk', add_zero]`. Introduce `γ hγ _`. Take `⟨-, ⟨g, hg⟩⟩` from `hγ`. Establish `e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g)`.

Establish `hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2` using `hg`. Use `show Matrix.GeneralLinearGroup.det γ.1.2 = _`. Rewrite using `[← hg']`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det = (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Simplify using `only [ld, e]`. Conclude with `hL.lgi _`. Conclude with `hL.lgcont.comp (hdet.comp hprj)`.
-/
theorem jCh : StdGood → BdetLaw → JTop → JCh := by
  intro hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ
  have hL : (adStd F).GoodL := hS F
  obtain ⟨-, -, -, -, hk, hd⟩ := hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) := by
    have h := Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F]))
      (Continuous.matrix_det continuous_id)
    convert h using 1
    funext x
    apply Units.ext
    rfl
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hfst : Continuous fun x : cover A ν ι => x.1.1 := continuous_fst.comp continuous_subtype_val
  have hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g := by
    intro p g
    simp only [ld, map_mul]
    exact hL.lgmul _ _
  have hK : ∀ k ∈ cK α j, ld k = 0 := by
    intro k hk'
    obtain ⟨κ, hκ, he⟩ := hk'.2
    have hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ := by
      rw [← he]
      simp [MulAut.conj_apply, map_mul, map_inv, mul_comm]
    have := hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ
    rw [hd] at this
    simp only [ld, hdk]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p _ q _
    simp [c0]
  · intro p _
    exact Circle.norm_coe _
  · intro γ hγ _
    obtain ⟨⟨x, hx⟩, -⟩ := hγ
    have := hG.toGoodL.χi x
    simp only [c0]
    have hx' : Units.map A.i.toMonoidHom x = γ.1.1 := hx
    rw [← hx', this]
    simp
  · exact (continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn
  · intro p _ g
    exact hadd p g
  · intro g k hk'
    rw [hadd, hK k hk', add_zero]
  · intro γ hγ _
    obtain ⟨-, ⟨g, hg⟩⟩ := hγ
    have e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      have hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2 := hg
      show Matrix.GeneralLinearGroup.det γ.1.2 = _
      rw [← hg']
      apply Units.ext
      show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det =
        (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det
      rw [RingHom.map_det]
      rfl
    simp only [ld, e]
    exact hL.lgi _
  · exact hL.lgcont.comp (hdet.comp hprj)

end GlobalTheory.CompanionTheory.EisSo
