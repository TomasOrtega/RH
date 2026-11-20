import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.LevZZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquivStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace PositivityTheory.RgUd.CellA

@[reducible] def XX (V W : Type) : Fin 2 → Type
  | 0 => V
  | 1 => W

instance instAddCommGroupXX {V W : Type} [AddCommGroup V] [AddCommGroup W] : ∀ a, AddCommGroup (XX V W a)
  | 0 => inferInstanceAs (AddCommGroup V)
  | 1 => inferInstanceAs (AddCommGroup W)

instance instModuleXX {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W] :
    ∀ a, Module ℂ (XX V W a)
  | 0 => inferInstanceAs (Module ℂ V)
  | 1 => inferInstanceAs (Module ℂ W)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def piPair (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) :
    ∀ a : Fin 2, Representation ℂ (GL (Fin (dd r m a)) k) (XX V W a)
  | 0 => A
  | 1 => x

/- English proof (translation)
The claim follows from `nonempty_prod₂_equiv_multiProd (k := k) (d := dd r m) (hdd r m) (piPair A x)`.
-/
theorem bridge_equiv (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) :
    Nonempty ((prod₂ A x).Equiv (multiProd (stdBlocks (dd r m) (hdd r m)) (piPair A x))) :=
  nonempty_prod₂_equiv_multiProd (k := k) (d := dd r m) (hdd r m) (piPair A x)

section Transport

variable {G V' W' : Type} [Group G] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Use `Submodule.subset_span ⟨n, f v, ?_⟩` and prove the remaining obligations. Use `show f (ρ n v - (χ n : ℂ) • v) = _`. Rewrite using `[map_sub, map_smul, f.isIntertwining]`.
-/
theorem twKer_le_comap {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (f : ρ.IntertwiningMap σ)
    (N : Subgroup G) (χ : N →* ℂˣ) : twKer ρ N χ ≤ (twKer σ N χ).comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨n, f v, ?_⟩
  show f (ρ n v - (χ n : ℂ) • v) = _
  rw [map_sub, map_smul, f.isIntertwining]

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (φ.isIntertwining' g) v`.
-/
theorem equiv_apply {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (φ : ρ.Equiv σ) (g : G) (v : V') :
    φ (ρ g v) = σ g (φ v) :=
  LinearMap.congr_fun (φ.isIntertwining' g) v

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `twKer_le_comap φ.symm.toIntertwiningMap N χ h`. Establish `e : φ.symm (φ v) = v` using `φ.toLinearEquiv.symm_apply_apply v`. Simplify `h2` using `[e]`.

Introduce `h`. Conclude with `twKer_le_comap φ.toIntertwiningMap N χ h`.
-/
theorem equiv_mem_twKer {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (φ : ρ.Equiv σ)
    (N : Subgroup G) (χ : N →* ℂˣ) (v : V') : φ v ∈ twKer σ N χ ↔ v ∈ twKer ρ N χ := by
  constructor
  · intro h
    have h2 := twKer_le_comap φ.symm.toIntertwiningMap N χ h
    have e : φ.symm (φ v) = v := φ.toLinearEquiv.symm_apply_apply v
    simpa [e] using h2
  · intro h
    exact twKer_le_comap φ.toIntertwiningMap N χ h

end Transport

/- English proof (translation)
Establish `key : piTensor (piPair A x) (levZ k r m z) = (ω z : ℂ) • LinearMap.id`. Use `PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, piTensor_tprod, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hv : (fun a => piPair A x a (levZ k r m z a) (v a)) = Function.update v 1 ((ω z : ℂ) • v 1)`. Use function extensionality and compare the values at `a`.

Use `fin_cases a`. Use `show A (levZ k r m z 0) (v 0) = Function.update v 1 ((ω z : ℂ) • v 1) 0`. Establish `h0 : A (levZ k r m z 0) = 1` using `map_one A`. Rewrite using `[h0, Function.update_of_ne (by decide)]`. Both sides reduce to the same expression.

Use `show x (levZ k r m z 1) (v 1) = Function.update v 1 ((ω z : ℂ) • v 1) 1`. Rewrite using `[Function.update_self]`. Conclude with `hx z (v 1)`. Rewrite using `[hv, MultilinearMap.map_update_smul, Function.update_eq_self]`. Rewrite using `[key]`.

Both sides reduce to the same expression.
-/
theorem piPair_levZ (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W)
    (ω : kˣ →* ℂˣ) (hx : HasCentralChar x ω) (z : kˣ) (t : ⨂[ℂ] a, XX V W a) :
    piTensor (piPair A x) (levZ k r m z) t = (ω z : ℂ) • t := by
  have key : piTensor (piPair A x) (levZ k r m z) = (ω z : ℂ) • LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, LinearMap.smul_apply, LinearMap.id_apply]
    have hv : (fun a => piPair A x a (levZ k r m z a) (v a)) = Function.update v 1 ((ω z : ℂ) • v 1) := by
      funext a
      fin_cases a
      · show A (levZ k r m z 0) (v 0) = Function.update v 1 ((ω z : ℂ) • v 1) 0
        have h0 : A (levZ k r m z 0) = 1 := map_one A
        rw [h0, Function.update_of_ne (by decide)]
        rfl
      · show x (levZ k r m z 1) (v 1) = Function.update v 1 ((ω z : ℂ) • v 1) 1
        rw [Function.update_self]
        exact hx z (v 1)
    rw [hv, MultilinearMap.map_update_smul, Function.update_eq_self]
  rw [key]
  rfl

/- English proof (translation)
Set `b` to `fun a => Module.Basis.ofVectorSpace ℂ (X a)`. Establish `hne : ∀ a, Nonempty (Module.Basis.ofVectorSpaceIndex ℂ (X a))` using `fun a => (b a).index_nonempty`. Set `p : ∀ a, Module.Basis.ofVectorSpaceIndex ℂ (X a)` to `fun a => (hne a).some`. Conclude with `nontrivial_of_ne _ 0 ((Basis.piTensorProduct b).ne_zero p)`.
-/
theorem nontrivial_piTensor {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  let b := fun a => Module.Basis.ofVectorSpace ℂ (X a)
  have hne : ∀ a, Nonempty (Module.Basis.ofVectorSpaceIndex ℂ (X a)) := fun a => (b a).index_nonempty
  let p : ∀ a, Module.Basis.ofVectorSpaceIndex ℂ (X a) := fun a => (hne a).some
  exact nontrivial_of_ne _ 0 ((Basis.piTensorProduct b).ne_zero p)

/- English proof (translation)
Take `⟨e⟩` from `GlobalTheory.T.twisted_jacquet_tensor_product_equiv (piPair A x) (fun a => unipB k (Fin (dd r m a))) (fun a => whitChar ψ (dd r m a))`. Establish `hf : ∀ a, Nontrivial (TwJacquet (piPair A x a) (unipB k (Fin (dd r m a))) (whitChar ψ (dd r m a)))`. Introduce `a`. Use `fin_cases a`. Conclude with `hA`.

Conclude with `hx`. Use `nontrivial_piTensor hf` as an intermediate fact. Establish `: Nontrivial (TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ))` using `e.toEquiv.nontrivial`. Take `⟨q, hq⟩` from `exists_ne (0 : TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ))`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Conclude with `⟨v, fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)⟩`.
-/
theorem exists_not_mem_twKer (ψ : AddChar k Circle) (A : Representation ℂ (GL (Fin r) k) V)
    (x : Representation ℂ (GL (Fin m) k) W) (hA : IsGenericFor ψ A) (hx : IsGenericFor ψ x) :
    ∃ v, v ∉ twKer (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_tensor_product_equiv (piPair A x) (fun a => unipB k (Fin (dd r m a))) (fun a => whitChar ψ (dd r m a))
  have hf : ∀ a, Nontrivial (TwJacquet (piPair A x a) (unipB k (Fin (dd r m a))) (whitChar ψ (dd r m a))) := by
    intro a
    fin_cases a
    · exact hA
    · exact hx
  have := nontrivial_piTensor hf
  have : Nontrivial (TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ)) :=
    e.toEquiv.nontrivial
  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ))
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨v, fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)⟩

end PositivityTheory.RgUd.CellA
