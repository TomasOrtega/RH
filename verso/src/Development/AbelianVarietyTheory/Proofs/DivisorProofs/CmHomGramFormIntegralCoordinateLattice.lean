import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddFirstSlotComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleScalarSecondSlotConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTripleStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.GramInt

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Introduce `n x y c hn hx hy`. Use `haveI := A.t.act.hom s`. Establish `hx' : (x ≫ A.t.act.act s) ^ n = 1` using `by rw [← pow_comp, hx]; simp`. Use `h n (x ≫ A.t.act.act s) y c hn hx' hy` as an intermediate fact. Simplify `this` using `only [Category.assoc, A.t.act.mul]`.
-/
theorem weilEq_act_left {A B : PAT H (Sp (𝓞 K))} {f g : A.t.G ⟶ B.t.G} {r : 𝓞 E} {k : Type} [Field k]
    {t : Sp k ⟶ Sp (𝓞 K)} (s : 𝓞 E) (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) t) :
    WeilEq B.t.PP.L (A.t.act.act s ≫ f) g A.t.PP.L (A.t.act.act (s * r)) (𝟙 _) t := by
  intro n x y c hn hx hy
  haveI := A.t.act.hom s
  have hx' : (x ≫ A.t.act.act s) ^ n = 1 := by rw [← pow_comp, hx]; simp
  have := h n (x ≫ A.t.act.act s) y c hn hx' hy
  simpa only [Category.assoc, A.t.act.mul] using this
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

/- English proof (translation)
The claim follows from `Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg) (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hF i`.
-/
theorem isLinearHom_finprod {I₀ : Type} (S : Finset I₀) (F : I₀ → (A.t.G ⟶ B.t.G))
    (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i)) :
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ S, F i) :=
  Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
    (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hF i

/- English proof (translation)
Proceed by induction on `hT using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simpa using h a`. Consider the case `cons a s has hs ih`. Rewrite using `[Finset.prod_cons, Finset.sum_cons]`. Conclude with `GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf.isMonHom (hG a).isMonHom (isLinearHom_finprod s G hG).isMonHom _ _ (h a) ih`.
-/
theorem weilEq_prod_right {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf.isMonHom (hG a).isMonHom
      (isLinearHom_finprod s G hG).isMonHom _ _ (h a) ih

/- English proof (translation)
Proceed by induction on `hS using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simpa using weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT`. Consider the case `cons a s has hs ih`. Rewrite using `[Finset.prod_cons, Finset.sum_cons]`. Conclude with `GlobalTheory.T.weilPairingCompatible_add_first_position_complex E H K σ₁ A B (F a) _ _ (hF a).isMonHom (isLinearHom_finprod s F hF).isMonHom (isLinearHom_finprod T G hG).isMonHom _ _ (weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT) ih`.
-/
theorem weilEq_prod_prod {I₀ J₀ : Type} (F : I₀ → (A.t.G ⟶ B.t.G)) (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i))
    (G : J₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ j, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G j)) (r : I₀ → J₀ → 𝓞 E)
    (h : ∀ i j, WeilEq B.t.PP.L (F i) (G j) A.t.PP.L (A.t.act.act (r i j)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {S : Finset I₀} (hS : S.Nonempty) {T : Finset J₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L (∏ i ∈ S, F i) (∏ j ∈ T, G j) A.t.PP.L (A.t.act.act (∑ i ∈ S, ∑ j ∈ T, r i j)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simpa using weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_first_position_complex E H K σ₁ A B (F a) _ _ (hF a).isMonHom (isLinearHom_finprod s F hF).isMonHom
      (isLinearHom_finprod T G hG).isMonHom _ _ (weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT) ih

/- English proof (translation)
Establish `e1 : f ^ n = ∏ _i ∈ Finset.range n, f` using `by simp`. Establish `e2 : g ^ m = ∏ _j ∈ Finset.range m, g` using `by simp`. Establish `e3 : ((n * m : ℕ) : 𝓞 E) * r = ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range m, r`. Simplify using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, e3]`. Conclude with `weilEq_prod_prod (fun _ => f) (fun _ => hf) (fun _ => g) (fun _ => hg) (fun _ _ => r) (fun _ _ => h) (Finset.nonempty_range_iff.2 hn.ne') (Finset.nonempty_range_iff.2 hm.ne')`.
-/
theorem weilEq_pow_pow (f g : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (hg : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act g) (r : 𝓞 E)
    (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    WeilEq B.t.PP.L (f ^ n) (g ^ m) A.t.PP.L (A.t.act.act ((n * m : ℕ) * r)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have e1 : f ^ n = ∏ _i ∈ Finset.range n, f := by simp
  have e2 : g ^ m = ∏ _j ∈ Finset.range m, g := by simp
  have e3 : ((n * m : ℕ) : 𝓞 E) * r = ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range m, r := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [e1, e2, e3]
  exact weilEq_prod_prod (fun _ => f) (fun _ => hf) (fun _ => g) (fun _ => hg) (fun _ _ => r) (fun _ _ => h)
    (Finset.nonempty_range_iff.2 hn.ne') (Finset.nonempty_range_iff.2 hm.ne')
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p : ℕ}

/- English proof (translation)
Establish `hne : (Finset.univ : Finset (Fin p)).Nonempty` using `Finset.univ_nonempty_iff.2 ⟨⟨0, hp⟩⟩`. Establish `hlin : ∀ (z : Fin p → 𝓞 E) a, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)` using `fun z a => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))`. Use `weilEq_prod_prod _ (hlin x) _ (hlin y) _ (fun a b => ?_) hne hne` and prove the remaining obligations. Establish `h1` using `weilEq_act_left (x a) (hG.1 a b)`. Conclude with `GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hlin x a).isMonHom (X.lin (Sum.inl b)).isMonHom _ (y b) h1`.
-/
theorem weilEq_combo (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (hp : 0 < p) (x y : Fin p → 𝓞 E) :
    WeilEq X.B.t.PP.L (∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a))
      (∏ b, ((X.A true).t.act.act (y b) ≫ GlobalTheory.FlatCM.phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hp⟩⟩
  have hlin : ∀ (z : Fin p → 𝓞 E) a, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act
      ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) := fun z a =>
    (GlobalTheory.Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))
  refine weilEq_prod_prod _ (hlin x) _ (hlin y) _ (fun a b => ?_) hne hne
  have h1 := weilEq_act_left (x a) (hG.1 a b)
  exact GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hlin x a).isMonHom (X.lin (Sum.inl b)).isMonHom _ (y b) h1

/- English proof (translation)
Break down `Nat.eq_zero_or_pos p with rfl | hp` into its components or cases. Conclude with `⟨0, by simp⟩`. Take `⟨n, hn, x, hx, f, hf, hfx⟩` from `hc`. Take `⟨m, hm, y, hy, g, hg, hgy⟩` from `hd`. Apply the tactic sequence `obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f g hf hg`.

Establish `h1` using `weilEq_pow_pow f g hf hg r hr hn hm`. Rewrite `h1` using `[hfx, hgy]`. Establish `h2` using `weilEq_combo X gP gQ hG hp x y`. Establish `h3 : WeilEq (X.A true).t.PP.L ((X.A true).t.act.act ((n * m : ℕ) * r)) (𝟙 _) (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K)))` using `fun k u v e hk hu hv => (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)`. Establish `h4` using `GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ h3`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `h5` using `congrArg (fun z : 𝓞 E => (z : E)) h4`. Simplify using `only [map_mul, map_natCast, map_sum] at h5`. Establish `hnm : ((n * m : ℕ) : E) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne'`. Apply `mul_left_cancel₀ hnm` to reduce the goal to its premises.

Rewrite using `[h5]`. Simplify using `only [hx, hy, ← hbar, map_mul, map_natCast, Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_of_coords (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (barE : E →+* E)
    (hbar : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) {c d : Fin p → E}
    (hc : c ∈ GlobalTheory.FlatCM.HomLat.coords X) (hd : d ∈ GlobalTheory.FlatCM.HomLat.coords X) :
    ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn, x, hx, f, hf, hfx⟩ := hc
  obtain ⟨m, hm, y, hy, g, hg, hgy⟩ := hd
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    f g hf hg
  have h1 := weilEq_pow_pow f g hf hg r hr hn hm
  rw [hfx, hgy] at h1
  have h2 := weilEq_combo X gP gQ hG hp x y
  have h3 : WeilEq (X.A true).t.PP.L ((X.A true).t.act.act ((n * m : ℕ) * r)) (𝟙 _) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)
  have h4 := GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ h3
  refine ⟨r, ?_⟩
  have h5 := congrArg (fun z : 𝓞 E => (z : E)) h4
  simp only [map_mul, map_natCast, map_sum] at h5
  have hnm : ((n * m : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne'
  apply mul_left_cancel₀ hnm
  rw [h5]
  simp only [hx, hy, ← hbar, map_mul, map_natCast, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end

/- English proof (translation)
Introduce `E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG barE hbar c hc d hd`. Establish `step : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)`. Introduce `c hc d hd`. Proceed by induction on `hd using Submodule.span_induction with`. Consider the case `mem d hd => exact integral_of_coords X gP gQ hG barE hbar hc hd`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add d d' _ _ h h'`. Take `⟨y, hy⟩` from `h`. Take `⟨y', hy'⟩` from `h'`. Use `⟨y + y', ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, hy, hy', Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Consider the case `smul s d _ h`. Take `⟨y, hy⟩` from `h`. Use `⟨H.bar s * y, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, ← hbar, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc => exact step c hc d hd`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add c c' _ _ h h'`. Take `⟨y, hy⟩` from `h`. Take `⟨y', hy'⟩` from `h'`. Use `⟨y + y', ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, hy, hy', Pi.add_apply, add_mul, Finset.sum_add_distrib]`.

Consider the case `smul s c _ h`. Take `⟨y, hy⟩` from `h`. Use `⟨s * y, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG barE hbar c hc d hd

  have step : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
      ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
    intro c hc d hd
    induction hd using Submodule.span_induction with
    | mem d hd => exact integral_of_coords X gP gQ hG barE hbar hc hd
    | zero => exact ⟨0, by simp⟩
    | add d d' _ _ h h' =>
      obtain ⟨y, hy⟩ := h
      obtain ⟨y', hy'⟩ := h'
      refine ⟨y + y', ?_⟩
      simp only [map_add, hy, hy', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul s d _ h =>
      obtain ⟨y, hy⟩ := h
      refine ⟨H.bar s * y, ?_⟩
      simp only [map_mul, ← hbar, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  induction hc using Submodule.span_induction with
  | mem c hc => exact step c hc d hd
  | zero => exact ⟨0, by simp⟩
  | add c c' _ _ h h' =>
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', hy'⟩ := h'
    refine ⟨y + y', ?_⟩
    simp only [map_add, hy, hy', Pi.add_apply, add_mul, Finset.sum_add_distrib]
  | smul s c _ h =>
    obtain ⟨y, hy⟩ := h
    refine ⟨s * y, ?_⟩
    simp only [map_mul, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.FlatCM.GramInt
end
