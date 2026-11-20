import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SubSub

/- English proof (translation)
The claim follows from `SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))`.
-/
theorem hom_ext_val' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ v : Fin (a + 1), ((f.toOrderHom v : Fin (b + 1)) : ℕ) = (g.toOrderHom v : Fin (b + 1))) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))

/- English proof (translation)
Unfold `Sx.along`. Rewrite using `[op_comp, E.map_comp]`. Both sides reduce to the same expression.
-/
theorem along_along' {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  unfold Sx.along
  rw [op_comp, E.map_comp]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_eq_along {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    x.sub j l h = x.along (SimplexCategory.subinterval j l h) := rfl

/- English proof (translation)
Unfold `Sx.along Sx.res`. Establish `h1` using `congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) ((E.map a.op).naturality g.op)) x`. Simplify `h1` using `only [ConcreteCategory.comp_apply]`.
-/
theorem res_along {E : Spc} {U V : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (g : V ⟶ U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.res g).along a = (x.along a).res g := by
  unfold Sx.along Sx.res
  have h1 := congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) ((E.map a.op).naturality g.op)) x
  simpa only [ConcreteCategory.comp_apply] using h1

/- English proof (translation)
Unfold `Sx.along Sx.map`. Use `f.naturality a.op` as an intermediate fact. Establish `h2` using `congrArg (fun φ => φ.app (op U)) this`. Simplify using `only [NatTrans.comp_app] at h2`. Conclude with `(congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) x).symm`.
-/
theorem map_along {E E' : Spc} {U : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (f : E ⟶ E')
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.map f).along a = (x.along a).map f := by
  unfold Sx.along Sx.map
  have := f.naturality a.op
  have h2 := congrArg (fun φ => φ.app (op U)) this
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) x).symm

/- English proof (translation)
Introduce `E U N x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j l j' l' h h'`. Rewrite using `[sub_eq_along, sub_eq_along, sub_eq_along, along_along']`. Use `congr 1`.

Conclude with `hom_ext_val' _ _ fun v => by show ((v : ℕ) + j') + j = v + (j + j')`. Use linear arithmetic over natural numbers and integers. Establish `: SimplexCategory.subinterval (n` using `N) 0 N (by omega) = 𝟙 _ := hom_ext_val' _ _ fun v => by show (v : ℕ) + 0 = v`. Use linear arithmetic over natural numbers and integers. Rewrite using `[sub_eq_along, this]`.

Unfold `Sx.along`. Simplify using the standard rewrite rules. Introduce `j l h`. Use `⟨fun g => res_along x g _, fun f => map_along x f _, rfl⟩` and prove the remaining obligations. Introduce `p r a b`.

Conclude with `along_along' x a b`.
-/
theorem main : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  intro E U N x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    rw [sub_eq_along, sub_eq_along, sub_eq_along, along_along']
    congr 1
    exact hom_ext_val' _ _ fun v => by
      show ((v : ℕ) + j') + j = v + (j + j')
      omega
  · have : SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ :=
      hom_ext_val' _ _ fun v => by
        show (v : ℕ) + 0 = v
        omega
    rw [sub_eq_along, this]
    unfold Sx.along
    simp
  · intro j l h
    refine ⟨fun g => res_along x g _, fun f => map_along x f _, rfl⟩
  · intro p r a b
    exact along_along' x a b

end GlobalTheory.EtC.SubSub
