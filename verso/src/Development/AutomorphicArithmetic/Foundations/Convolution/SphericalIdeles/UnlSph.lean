import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.NoLinkRev
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.IsSmoothCharUnr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

namespace UpperTheory.ConvolutionTheory.Sph.UnramifiedSpherical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `x : Fin n → IrrGL k` to `fun i => IrrGL.ofChar (χ i) (hχ i)`. Establish `hx : ∀ i, (x i).IsCusp` using `fun i => IrrGL.isCusp_ofChar _ _`. Establish `hd : ∑ i, (x i).1 = n` using `by simp [x, IrrGL.ofChar]`. Establish `hnu : ∀ i j, x j ≠ (x i).nu 1` using `fun i j e => by`. Simplify using `only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e`.

Conclude with `h i j e`. Establish `hnl : ∀ i j, ¬ (Segment.single (x i) (hx i)).Linked (Segment.single (x j) (hx j))` using `fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i)`. Establish `hP : (prodIrr x hd).IsIrreducible` using `GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd hnl (fun i => (single_spec (hx i)).2.1)`. Take `⟨p⟩` from `(Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) (stdBlocks (fun i => (x i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (χ i))`. Set `q` to `multiProdEquiv (stdBlocks (fun i => (x i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (χ i) (hχ i))`.

Establish `hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP`. Use `haveI := nontrivial_of_irreducible hM`. Use `haveI := nontrivial_of_isSubquotient (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) χ)`. Take `⟨e⟩` from `equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ) hM`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv e hM`.
-/
private theorem prin_irr {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (h : ∀ i j, χ j ≠ χ i * absPow k 1) : (prinSeries χ).IsIrreducible := by
  let x : Fin n → IrrGL k := fun i => IrrGL.ofChar (χ i) (hχ i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by simp [x, IrrGL.ofChar]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hnl : ∀ i j, ¬ (Segment.single (x i) (hx i)).Linked (Segment.single (x j) (hx j)) := fun i j =>
    GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd hnl
      (fun i => (single_spec (hx i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun i => (x i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (χ i))
  let q := multiProdEquiv (stdBlocks (fun i => (x i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (χ i) (hχ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI := nontrivial_of_isSubquotient
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) χ)
  obtain ⟨e⟩ := equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv e hM

/- English proof (translation)
Introduce `e`. Take `⟨ϖ, hϖ⟩` from `GlobalTheory.PrinTwo.NoFix.exists_unif k`. Establish `e'` using `congrArg (fun χ : kˣ →* ℂˣ => ((χ ϖ : ℂˣ) : ℂ)) e`. Simplify using `only [MonoidHom.mul_apply, Units.val_mul] at e'`. Rewrite `e'` using `[unrChar_uniformizer k b hϖ, unrChar_uniformizer k a hϖ, val_absPow]`.

Establish `hn : nabs k ϖ = (resCard k : ℝ)⁻¹`. Rewrite using `[GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]`. Simplify using the standard rewrite rules. Establish `hq : (resCard k : ℂ) ≠ 0`. Establish `: (1 : ℝ) < resCard k` using `by exact_mod_cast one_lt_resCard (k := k)`.

Conclude with `(by positivity : (resCard k : ℝ) ≠ 0)` after adjusting the coercions. Rewrite `e'` using `[Complex.cpow_one, hn]`. Apply `h` to reduce the goal to its premises. Rewrite using `[e']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
private theorem unr_ne {a b : ℂˣ} (h : (a : ℂ) ≠ (resCard k : ℂ) * b) : unrChar k b ≠ unrChar k a * absPow k 1 := by
  intro e
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have e' := congrArg (fun χ : kˣ →* ℂˣ => ((χ ϖ : ℂˣ) : ℂ)) e
  simp only [MonoidHom.mul_apply, Units.val_mul] at e'
  rw [unrChar_uniformizer k b hϖ, unrChar_uniformizer k a hϖ, val_absPow] at e'
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [Complex.cpow_one, hn] at e'
  apply h
  rw [e']
  push_cast
  field_simp

/- English proof (translation)
Unfold `IsSpherical IsSphericalFor at *`. Take `⟨x, hx, h0⟩` from `(Submodule.ne_bot_iff _).1 h`. Use `(Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv x, fun g => ?_, fun h1 => h0 (e.toLinearEquiv.injective (by rw [h1, map_zero]))⟩` and prove the remaining obligations. Establish `hint : e.toLinearEquiv (ρ (g : GL (Fin n) k) x) = π (g : GL (Fin n) k) (e.toLinearEquiv x)` using `LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin n) k)) x`. Establish `hg` using `hx g`.

Rewrite using `[← hint, hg, map_smul]`.
-/
private theorem sph_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {π : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv x, fun g => ?_, fun h1 =>
    h0 (e.toLinearEquiv.injective (by rw [h1, map_zero]))⟩
  have hint : e.toLinearEquiv (ρ (g : GL (Fin n) k) x) = π (g : GL (Fin n) k) (e.toLinearEquiv x) :=
    LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin n) k)) x
  have hg := hx g
  rw [← hint, hg, map_smul]

end UpperTheory.ConvolutionTheory.Sph.UnramifiedSpherical

/- English proof (translation)
Introduce `K _ _ n v τ α h hs`. Establish `hq : (resCard (v.adicCompletion K) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ)`. Use `GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm K v` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hI` using `UnramifiedSpherical.prin_irr (k := v.adicCompletion K) (fun i => unrChar (v.adicCompletion K) (α i)) (fun i => PositivityTheory.Rg.BcB.N3.Pus.isSmoothChar_unr (α i)) (fun i j => UnramifiedSpherical.unr_ne (by rw [hq]; exact h i j))`.

Take `⟨e⟩` from `hs.nonempty_equiv τ.irred hI`. Conclude with `UnramifiedSpherical.sph_of_equiv e (PositivityTheory.Rg.BcB.N3.Pse.iP_sph (k := v.adicCompletion K) α)`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.unlSph :
    UpperTheory.ConvolutionTheory.Sph.UnlSph := by
  intro K _ _ n v τ α h hs
  have hq : (resCard (v.adicCompletion K) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) := by
    have := GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm K v
    exact_mod_cast this
  have hI := UnramifiedSpherical.prin_irr (k := v.adicCompletion K) (fun i => unrChar (v.adicCompletion K) (α i))
    (fun i => PositivityTheory.Rg.BcB.N3.Pus.isSmoothChar_unr (α i))
    (fun i j => UnramifiedSpherical.unr_ne (by rw [hq]; exact h i j))
  obtain ⟨e⟩ := hs.nonempty_equiv τ.irred hI
  exact UnramifiedSpherical.sph_of_equiv e (PositivityTheory.Rg.BcB.N3.Pse.iP_sph (k := v.adicCompletion K) α)
