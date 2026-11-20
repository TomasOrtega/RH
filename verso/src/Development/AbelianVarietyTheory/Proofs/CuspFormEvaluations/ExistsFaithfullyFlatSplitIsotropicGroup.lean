import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentativesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `h0 : ev 0 = 1`. Use `h 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.mp this`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro f`. Simplify using `[h0]`. Consider the case `succ n ih => intro f`. Rewrite using `[Fin.sum_univ_succ, h, ih, List.ofFn_succ, List.prod_cons]`.
-/
theorem map_sum_eq_prod_ofFn_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) :
    ∀ (n : ℕ) (f : Fin n → A), ev (∑ j, f j) = (List.ofFn fun j => ev (f j)).prod := by
  have h0 : ev 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.mp this
  intro n
  induction n with
  | zero => intro f; simp [h0]
  | succ n ih => intro f; rw [Fin.sum_univ_succ, h, ih, List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `h 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Simplify using `using left_eq_mul.mp this`.

Consider the case `succ k ih => rw [succ_nsmul, h, ih, pow_succ]`.
-/
theorem map_nsmul_eq_pow_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) (a : A) (k : ℕ) : ev (k • a) = ev a ^ k := by
  induction k with
  | zero =>
    have := h 0 0
    rw [add_zero] at this
    simpa using left_eq_mul.mp this
  | succ k ih => rw [succ_nsmul, h, ih, pow_succ]

/- English proof (translation)
Introduce `hL E _ _ _ H Dw l Xo S _ x0 n Λ N hU hN hle`. Take `⟨B, iB, φ, ev, hff, hadd, hsm, hk, hinj⟩` from `GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure hL E H Dw l Xo S x0 (N ^ 2) (pow_pos hN 2)`. Take `⟨zz, hz, hzi, -⟩` from `GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN hle`. Use `⟨B, iB, φ, fun i b => ev (zz i b), hff, fun i => ⟨fun b => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]`.

Introduce `mu hmu cm hcm i'`. Establish `h1` using `hz i mu hmu cm hcm i'`. Simplify using `only [← hsm]`. Rewrite using `[← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd]`. Take `⟨y, hy⟩` from `h1`.

Rewrite using `[hy]`. Conclude with `hk y`. Introduce `k _ ψ g hg i i' hii`. Apply `hzi` to reduce the goal to its premises. Introduce `b`.

Apply `hinj k ψ` to reduce the goal to its premises. Use `congrArg (fun f => f.left) (congrFun hii b)` as an intermediate fact. Simplify using `only [Over.comp_left, hg] at this`. Conclude with `this`.
-/
theorem exists_faithfullyFlat_split_Zh : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  intro hL E _ _ _ H Dw l Xo S _ x0 n Λ N hU hN hle
  obtain ⟨B, iB, φ, ev, hff, hadd, hsm, hk, hinj⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure hL E H Dw l Xo S x0 (N ^ 2) (pow_pos hN 2)
  obtain ⟨zz, hz, hzi, -⟩ := GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN hle
  refine ⟨B, iB, φ, fun i b => ev (zz i b), hff, fun i => ⟨fun b => ?_, ?_⟩, ?_⟩
  · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
  · intro mu hmu cm hcm i'
    have h1 := hz i mu hmu cm hcm i'
    simp only [← hsm]
    rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd]
    obtain ⟨y, hy⟩ := h1
    rw [hy]
    exact hk y
  · intro k _ ψ g hg i i' hii
    apply hzi
    intro b
    apply hinj k ψ
    have := congrArg (fun f => f.left) (congrFun hii b)
    simp only [Over.comp_left, hg] at this
    exact this

end GlobalTheory
