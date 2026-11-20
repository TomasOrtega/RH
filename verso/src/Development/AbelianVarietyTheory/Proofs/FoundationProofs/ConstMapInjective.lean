import Mathlib
import Formalism.SharpRestriction.GrowthBounds.DataG

open Formalism.MainNotions.G MvPolynomial

noncomputable section

namespace GlobalTheory.PrescribedRank

variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def noPlaces : Places p O Kf where
  w := 0
  nV := 0
  n' := fun _ => 0
  W := fun _ => O
  Qq := fun _ => Kf
  ι := fun _ => RingHom.id Kf
  σ := fun _ => RingEquiv.refl Kf
  j := fun _ => RingHom.id O
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun _ _ _ => 0
  dom := fun v => v.elim0

instance : IsEmpty (Fin (noPlaces p O Kf).nV) := inferInstanceAs (IsEmpty (Fin 0))

def trivLevel : Level (noPlaces p O Kf) where
  Γ := PUnit
  act := fun _ => 1
  χ := 1

/- English proof (translation)
The claim follows from `funext fun v => isEmptyElim v`.
-/
theorem tup_eq (L L' : (noPlaces p O Kf).Tup) : L = L' := funext fun v => isEmptyElim v

/- English proof (translation)
Introduce `v` and use `isEmptyElim v`.
-/
theorem isLatTup (L : (noPlaces p O Kf).Tup) : (noPlaces p O Kf).IsLatTup L := fun v => isEmptyElim v

/- English proof (translation)
Establish `h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _` using `fun G => MvPolynomial.algHom_ext fun i => isEmptyElim i.1`. Unfold `Level.actX Places.natAct`. Rewrite using `[h, Fintype.prod_empty]`. Simplify using the standard rewrite rules.
-/
theorem actX_apply (γ : (trivLevel p O Kf).Γ) (x : (noPlaces p O Kf).Xsp) :
    (trivLevel p O Kf).actX γ x = x := by
  have h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _ := fun G =>
    MvPolynomial.algHom_ext fun i => isEmptyElim i.1
  unfold Level.actX Places.natAct
  rw [h, Fintype.prod_empty]
  simp

/- English proof (translation)
Unfold `Places.HtupW Places.tenV`. Use `congr 1`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, -, rfl⟩`.

Rewrite using `[Fintype.prod_empty]`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩`.
-/
theorem htupW_eq (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    rw [Fintype.prod_empty]
    rfl
  · rintro rfl
    exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩

/- English proof (translation)
Unfold `Level.funMod`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h, -⟩, -⟩ L`. Conclude with `h L (isLatTup p O Kf L)`.

Introduce `h`. Use `⟨⟨fun L _ => h L, fun L hL => absurd (isLatTup p O Kf L) hL⟩, fun γ L => ?_⟩` and prove the remaining obligations. Establish `hχ : (trivLevel p O Kf).χ γ = 1` using `rfl`. Rewrite using `[tup_eq p O Kf ((trivLevel p O Kf).smul γ L) L, hχ]`. Simplify using `[actX_apply]`.
-/
theorem mem_funMod (Hv : (noPlaces p O Kf).Tup → Submodule O (noPlaces p O Kf).Xsp)
    (F : (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) :
    F ∈ (trivLevel p O Kf).funMod Hv ↔ ∀ L, F L ∈ Hv L := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩ L
    exact h L (isLatTup p O Kf L)
  · intro h
    refine ⟨⟨fun L _ => h L, fun L hL => absurd (isLatTup p O Kf L) hL⟩, fun γ L => ?_⟩
    have hχ : (trivLevel p O Kf).χ γ = 1 := rfl
    rw [tup_eq p O Kf ((trivLevel p O Kf).smul γ L) L, hχ]
    simp [actX_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ => ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩`.
-/
theorem finClasses : (trivLevel p O Kf).FinClasses :=
  ⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ =>
    ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩

def gat (d : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := noPlaces p O Kf
  comp := Fin d
  lev := fun _ => trivLevel p O Kf
  e := 0

def constMap (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) where
  toFun c := fun i _ => c i • (1 : (noPlaces p O Kf).Xsp)
  map_add' a b := by
    funext i L
    simp [add_smul]
  map_smul' a b := by
    funext i L
    simp [mul_smul]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Use function extensionality and compare the values at `i`. Establish `h : c i • (1 : (noPlaces p O Kf).Xsp) = 0` using `congrFun (congrFun hc i) (fun v => isEmptyElim v)`. Establish `h2` using `congrArg (MvPolynomial.coeff 0) h`.

Rewrite `h2` using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero, Algebra.smul_def, mul_one]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
theorem constMap_injective (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h : c i • (1 : (noPlaces p O Kf).Xsp) = 0 := congrFun (congrFun hc i) (fun v => isEmptyElim v)
  have h2 := congrArg (MvPolynomial.coeff 0) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero,
    Algebra.smul_def, mul_one] at h2
  apply hinj
  rw [h2]
  simp

/- English proof (translation)
Use extensionality with `F`. Rewrite using `[Submodule.mem_pi]`. Simplify using `only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ i L`.

Conclude with `⟨c i, rfl⟩`. Introduce `h choose c hc using h`. Use `⟨fun i => c i (fun v => isEmptyElim v), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i L`. Rewrite using `[tup_eq p O Kf L (fun v => isEmptyElim v)]`.

Conclude with `hc i _`.
-/
theorem range_constMap (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by
  ext F
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ i L
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    refine ⟨fun i => c i (fun v => isEmptyElim v), ?_⟩
    funext i L
    rw [tup_eq p O Kf L (fun v => isEmptyElim v)]
    exact hc i _

/- English proof (translation)
Establish `h : (gat p O Kf d).d = Module.finrank O (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW)` using `rfl`. Rewrite using `[h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]`. Simplify using the standard rewrite rules.
-/
theorem gat_d (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) : (gat p O Kf d).d = d := by
  have h : (gat p O Kf d).d = Module.finrank O
      (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW) := rfl
  rw [h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]
  simp

/- English proof (translation)
Introduce `p d hp`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Conclude with `⟨gat p ℤ_[p] ℚ_[p] d, gat_d p _ _ d (IsFractionRing.injective ℤ_[p] ℚ_[p]), fun _ => finClasses p _ _⟩`.
-/
theorem GAtP₂ : ∀ (p d : ℕ), p.Prime → ∃ G : GAtP p, G.d = d ∧ G.FinClasses := by
  intro p d hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨gat p ℤ_[p] ℚ_[p] d, gat_d p _ _ d (IsFractionRing.injective ℤ_[p] ℚ_[p]),
    fun _ => finClasses p _ _⟩

end GlobalTheory.PrescribedRank
