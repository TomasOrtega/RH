import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.Gen.BaseChange

/- English proof (translation)
Introduce `hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M`. Take `⟨o', ⟨mo⟩⟩` from `exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ`. Set `U : GObj gb₂ N (pullback.snd M.s (spMap τ))` to `up hρ ht pullback.condition.symm o'`. Establish `hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'), ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j)`. Introduce `S s' o`.

Set `u : GObj gb₁ N (s' ≫ spMap τ)` to `down hρ ht rfl o`. Take `⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩` from `M.rep S _ u`. Set `j : S ⟶ pullback M.s (spMap τ)` to `pullback.lift a s' ha`. Establish `j₁ : j ≫ pullback.fst M.s (spMap τ) = a` using `pullback.lift_fst _ _ _`. Establish `j₂ : j ≫ pullback.snd M.s (spMap τ) = s'` using `pullback.lift_snd _ _ _`.

Take `⟨mj, -⟩` from `(hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)`. Establish `mj' : GObjMap o U j` using `⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩`. Use `⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `j' ⟨h₂, ⟨m'⟩⟩`. Establish `m'' : GObjMap u o' j'` using `⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩`.

Take `⟨n, -⟩` from `(hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''`. Establish `e : j' ≫ pullback.fst M.s (spMap τ) = a` using `hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[e, j₁]`. Rewrite using `[h₂, j₂]`.

Use `⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ), IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩` and prove the remaining obligations.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.modelBc_of :
    MapEq → ModelBc := by
  intro hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M
  obtain ⟨o', ⟨mo⟩⟩ := exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ
  let U : GObj gb₂ N (pullback.snd M.s (spMap τ)) := up hρ ht pullback.condition.symm o'
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'),
      ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j) := by
    intro S s' o
    let u : GObj gb₁ N (s' ≫ spMap τ) := down hρ ht rfl o
    obtain ⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩ := M.rep S _ u
    let j : S ⟶ pullback M.s (spMap τ) := pullback.lift a s' ha
    have j₁ : j ≫ pullback.fst M.s (spMap τ) = a := pullback.lift_fst _ _ _
    have j₂ : j ≫ pullback.snd M.s (spMap τ) = s' := pullback.lift_snd _ _ _
    obtain ⟨mj, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)
    have mj' : GObjMap o U j := ⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩
    refine ⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩
    rintro j' ⟨h₂, ⟨m'⟩⟩
    have m'' : GObjMap u o' j' := ⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩
    obtain ⟨n, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''
    have e : j' ≫ pullback.fst M.s (spMap τ) = a :=
      hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩
    apply pullback.hom_ext
    · rw [e, j₁]
    · rw [h₂, j₂]
  refine ⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ),
    IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩
