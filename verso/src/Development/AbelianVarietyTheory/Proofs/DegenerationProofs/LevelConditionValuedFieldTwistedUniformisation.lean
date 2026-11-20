import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait.LevelClause

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `e`. Use `⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩` and prove the remaining obligations. Rewrite using `[hp.1, hq.1]`. Conclude with `h1`. Rewrite using `[hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]`.

Both sides reduce to the same expression. Establish `e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ` using `N.twist_τ β u z χ`. Establish `e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ`. Rewrite using `[map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul, zpow_natCast, h]`. Establish `e₃ : (p'.1.2 * (N.twist β u).io z).s χ = p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z)` using `rfl`.

Use `(hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)` and prove the remaining obligations. Rewrite using `[h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div]`. Normalize the expressions using the abelian group laws.
-/
theorem qEq_twist {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {u r : Oˣ} {j : ℕ} (h : r ^ j = u)
    {p q : N.QT j} {p' q' : (N.twist β u).QT j} (e : N.QEq p q) (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩
  · rw [hp.1, hq.1]; exact h1
  · rw [hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]; rfl
  · have e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ := N.twist_τ β u z χ
    have e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ := by
      rw [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul,
        zpow_natCast, h]
    have e₃ : (p'.1.2 * (N.twist β u).io z).s χ =
        p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z) := rfl
    refine (hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)
    rw [h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

/- English proof (translation)
Set `I` to `NumD.Hom.ofIso J`. Establish `hp : p.1.2 ^ k = N.io p.1.1.toAdd` using `p.2`. Use `⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩` and prove the remaining obligations. Establish `a` using `(I.rel_img p.1.2).pow k`. Rewrite `a` using `[hp]`.

Conclude with `(I.rel_existsUnique _).unique a (I.rel_io _)`.
-/
theorem exists_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩
  have a := (I.rel_img p.1.2).pow k
  rw [hp] at a
  exact (I.rel_existsUnique _).unique a (I.rel_io _)

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `e`. Set `I` to `NumD.Hom.ofIso J`. Use `⟨J.e z, by rw [hq, hp, h1, map_add, map_nsmul], ?_⟩` and prove the remaining obligations. Establish `a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z))` using `NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)`. Rewrite `a` using `[← h2]`.

Conclude with `(I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a`.
-/
theorem qEq_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (e : N.QEq p q) (hp : p'.1.1.toAdd = J.e p.1.1.toAdd) (hp' : J.Rel p.1.2 p'.1.2)
    (hq : q'.1.1.toAdd = J.e q.1.1.toAdd) (hq' : J.Rel q.1.2 q'.1.2) : N'.QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, by rw [hq, hp, h1, map_add, map_nsmul], ?_⟩
  have a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z)) := NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)
  rw [← h2] at a
  exact (I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a

/- English proof (translation)
Take `rfl : pt₀ = fun k => pt k ≫ φ` from `funext fun k => (hpt k).symm`. Establish `z : Sp F` using `(default : PrimeSpectrum F)`. Rewrite using `[genRel_iff w t t₀ x z]`. Use `⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩` and prove the remaining obligations. Establish `hJ` using `fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)`.

Establish `hJ'` using `fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)`. Establish `hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀` using `Set.mem_iInter.2 h₀`. Establish `hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ))` using `Set.mem_iInter.2 fun k => hJ _`. Establish `hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j` using `Set.mem_iInter.2 h₁`. Establish `hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k))` using `Set.mem_iInter.2 fun k => hJ' _`.

Establish `P1` using `pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'`. Establish `G1` using `gen_trans ht (𝟙 _) z hq hq'`. Establish `G0` using `gen_trans ht₀ (𝟙 _) z hp hp'`. Establish `a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) = (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val` using `fun k => toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _`. Establish `a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) = (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val`.

Simplify using `only [pw, Category.id_comp]`. Rewrite using `[map_prod, Units.coe_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0` using `fun h0 => by`. Use `a₃ k` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `Units.ne_zero _ this.symm`. Establish `e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _` using `Units.ext (a₃ k)`. Rewrite using `[← e, ← map_zpow]`. Use `show _ = toStk z _`.

Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Establish `e'` using `congrArg (toStk z) hv`. Rewrite `e'` using `[map_mul, map_mul, a₄]`. Establish `b₁ : toStk z (vF t (𝟙 _) J') = _` using `toStk_valF _ _ z hq' _`. Establish `b₀ : toStk z (vF t₀ (𝟙 _) J) = _` using `toStk_valF _ _ z hp' _`.

Rewrite `e'` using `[b₁, b₀, ← Units.val_mul]`. Establish `hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j`. Simplify using `only [pw, Category.id_comp]`. Establish `step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d)` using `fun a b c d => by`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Rewrite using `[hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]`. Conclude with `mul_left_comm _ _ _`.
-/
theorem genRel_of_gauge {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (ht₀ : t₀.IsGen) (x : F) (hpt : ∀ k, pt k ≫ φ = pt₀ k)
    (J : (Sp F ⟶ B₀) → M₀.ι) (J' : (Sp F ⟶ B) → M.ι) (gJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M₀.U (J ψ)) (gJ' : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M.U (J' ψ))
    (hv : (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) * vF t (𝟙 _) J' = x * vF t₀ (𝟙 _) J) :
    GenRel w t t₀ x := by
  obtain rfl : pt₀ = fun k => pt k ≫ φ := funext fun k => (hpt k).symm
  have z : Sp F := (default : PrimeSpectrum F)
  rw [genRel_iff w t t₀ x z]
  refine ⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩
  have hJ := fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)
  have hJ' := fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)
  have hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ _
  have hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k)) := Set.mem_iInter.2 fun k => hJ' _
  have P1 := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'
  have G1 := gen_trans ht (𝟙 _) z hq hq'
  have G0 := gen_trans ht₀ (𝟙 _) z hp hp'
  have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) =
      (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val := fun k =>
    toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _
  have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) =
      (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val := by
    simp only [pw, Category.id_comp]
    rw [map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0 := fun h0 => by
      have := a₃ k
      rw [h0, map_zero] at this
      exact Units.ne_zero _ this.symm
    have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _ := Units.ext (a₃ k)
    rw [← e, ← map_zpow]
    show _ = toStk z _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e' := congrArg (toStk z) hv
  rw [map_mul, map_mul, a₄] at e'
  have b₁ : toStk z (vF t (𝟙 _) J') = _ := toStk_valF _ _ z hq' _
  have b₀ : toStk z (vF t₀ (𝟙 _) J) = _ := toStk_valF _ _ z hp' _
  rw [b₁, b₀, ← Units.val_mul] at e'
  have hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j := by
    simp only [pw, Category.id_comp]
  have step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d) := fun a b c d => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]
  exact mul_left_comm _ _ _

/- English proof (translation)
Use `fin_cases i`. Use `show _ = (ν.eA (N.c χ * b)).left`. Rewrite using `[map_mul, ν.c_eq]`. Both sides reduce to the same expression. Use `show _ = (ν.eA (N.c χ)).left`.

Rewrite using `[ν.c_eq]`. Both sides reduce to the same expression. Both sides reduce to the same expression. Use `show _ = (ν.eA 1).left`. Rewrite using `[map_one]`.

Both sides reduce to the same expression.
-/
theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) (b : N.A) (χ : N.X) (i : Fin 4) :
    DegPre.gtφ D F (ν.eA b) (ν.eX χ) i = (ν.eA (![N.c χ * b, N.c χ, b, 1] i)).left := by
  fin_cases i
  · show _ = (ν.eA (N.c χ * b)).left
    rw [map_mul, ν.c_eq]; rfl
  · show _ = (ν.eA (N.c χ)).left
    rw [ν.c_eq]; rfl
  · rfl
  · show _ = (ν.eA 1).left
    rw [map_one]; rfl

/- English proof (translation)
Introduce `_ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz`. Take `⟨-, hw, hA, hX, hne, hh⟩` from `hF`. Establish `hrk` using `hr.pow hk`. Take `⟨q₀, hq₀, -⟩` from `TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C) (RingHom.ext fun _ => rfl) p₀`. Take `⟨-, -, -, -, B₀⟩` from `hBr O' a.D₀ a.even a.bimult C A.N A.ν`.

Take `⟨-, -, -, -, B₁⟩` from `hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'`. Take `⟨v₀, hv₀, -⟩` from `(B₀ k).1 q₀`. Establish `e₀` using `((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)`. Take `⟨t₀, ht₀, -⟩` from `existsUnique_twRel A.be u (r k) hrk v₀`. Take `⟨t₁, ht₁, -⟩` from `existsUnique_twRel A.be u (r k) hrk (A.q k v)`.

Take `⟨s₀, hs₀, hs₀'⟩` from `exists_image J t₀`. Take `⟨s₁, hs₁, hs₁'⟩` from `exists_image J t₁`. Take `⟨q, hq⟩` from `(B₁ k).2.1 s₀`. Take `⟨p', hp'⟩` from `(B₁ k).2.1 s₁`. Establish `e₁` using `((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')`.

Use `⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]`. Both sides reduce to the same expression. Take `⟨χ, rfl⟩` from `A.ν.eX.surjective χ`. Establish `hb : q.g.b = ν'.eA (J.φ v₀.1.2.b)` using `by rw [← hq.2.1, hs₀'.1, ht₀.2.1]`.

Establish `hc : N'.c (J.e χ) = J.φ (A.N.c χ)` using `J.c_eq χ`. Establish `g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i = (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left` using `fun i => by`. Rewrite using `[hb, hX, gtφ_eq, hc]`. Use `fin_cases i`. Conclude with `congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm`.

Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm`. Use `genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_` and prove the remaining obligations. Rewrite using `[g₁, hA, ← hv₀.2.1, gtφ_eq]`.

Establish `g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _ (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ), ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val = wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] …` using `fun i => congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)`. Establish `g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C)` using `(congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm`. Establish `g₄` using `(hv₀.2.2 χ).symm`. Establish `g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ)`. Rewrite using `[← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, A.be.div_mul hkM]`.

Establish `g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) = v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b`. Use `hs₀'.2 χ` as an intermediate fact. Rewrite `this` using `[ht₀.2.1, ht₀.2.2]`. Conclude with `this`. Establish `g₇` using `congrArg Units.val g₆`.

Simplify using `only [Units.val_mul] at g₇`. Use `(congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_four]`. Establish `alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W → w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ → w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀`. Introduce `S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄`.

Substitute `a₃` using the available equality. Simplify using `only [zpow_neg, zpow_one]`. Clear the denominators using the available nonvanishing facts. Use `mul_left_cancel₀ nW ?_` and prove the remaining obligations. Take the linear combination `(-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ + (S₀ * ρ * w₀ * w₃) * a₂`.

Conclude with `alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _) (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇`. Take `⟨g, hg, -, hge, -⟩` from `hTI C k hk`. Conclude with `(hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)`.
-/
theorem level_clause : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  intro _ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz
  obtain ⟨-, hw, hA, hX, hne, hh⟩ := hF
  have hrk := hr.pow hk
  obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C)
    (RingHom.ext fun _ => rfl) p₀
  obtain ⟨-, -, -, -, B₀⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B₁⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨v₀, hv₀, -⟩ := (B₀ k).1 q₀
  have e₀ := ((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_twRel A.be u (r k) hrk v₀
  obtain ⟨t₁, ht₁, -⟩ := existsUnique_twRel A.be u (r k) hrk (A.q k v)
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_image J t₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_image J t₁
  obtain ⟨q, hq⟩ := (B₁ k).2.1 s₀
  obtain ⟨p', hp'⟩ := (B₁ k).2.1 s₁
  have e₁ := ((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')
  refine ⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩
  · rw [← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]
    rfl
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective χ
    have hb : q.g.b = ν'.eA (J.φ v₀.1.2.b) := by rw [← hq.2.1, hs₀'.1, ht₀.2.1]
    have hc : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
    have g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i =
        (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left := fun i => by
      rw [hb, hX, gtφ_eq, hc]
      fin_cases i
      · exact congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm
      · rfl
      · rfl
      · exact congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm
    refine genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_
    · rw [g₁, hA, ← hv₀.2.1, gtφ_eq]
    · have g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _
          (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ),
            ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val =
          wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i)) := fun i =>
        congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)
      have g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C) :=
        (congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm
      have g₄ := (hv₀.2.2 χ).symm
      have g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ) := by
        rw [← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
          mul_comm, A.be.div_mul hkM]
      have g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) =
          v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b := by
        have := hs₀'.2 χ
        rw [ht₀.2.1, ht₀.2.2] at this
        exact this
      have g₇ := congrArg Units.val g₆
      simp only [Units.val_mul] at g₇
      refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)
      rw [Fin.prod_univ_four]
      have alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W →
          w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ →
          w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀ := by
        intro S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄
        subst a₃
        simp only [zpow_neg, zpow_one]
        field_simp
        refine mul_left_cancel₀ nW ?_
        linear_combination (-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ +
          (S₀ * ρ * w₀ * w₃) * a₂
      exact alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _)
        (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇
  · obtain ⟨g, hg, -, hge, -⟩ := hTI C k hk
    exact (hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)

end GlobalTheory.Ex.Trait.LevelClause
end
