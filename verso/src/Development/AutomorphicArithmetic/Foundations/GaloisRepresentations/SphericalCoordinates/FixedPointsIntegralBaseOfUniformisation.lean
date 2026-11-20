import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Take `⟨k, rfl⟩` from `hd`. Introduce `u hu`. Establish `hu' : L.CongOne (N * k) u ∧ L.CongOne (N * k) u⁻¹` using `hu`. Use `show L.CongOne N u ∧ L.CongOne N u⁻¹`. Use `⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw, e⟩` from `hu'.1 v hv`. Conclude with `⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩`. Take `⟨w, hw, e⟩` from `hu'.2 v hv`. Conclude with `⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩`.
-/
private theorem kn_anti {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') : L.KN N' ≤ L.KN N := by
  obtain ⟨k, rfl⟩ := hd
  intro u hu
  have hu' : L.CongOne (N * k) u ∧ L.CongOne (N * k) u⁻¹ := hu
  show L.CongOne N u ∧ L.CongOne N u⁻¹
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, e⟩ := hu'.1 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩
  · obtain ⟨w, hw, e⟩ := hu'.2 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

/- English proof (translation)
Introduce `u hu g`. Establish `a : h * u⁻¹ * h⁻¹ ∈ L.KN N` using `hc _ (inv_mem hu)`. Establish `b : u ∈ L.KN N` using `kn_anti L hd hu`. Establish `e : h * (u⁻¹ * g * u) = (h * u⁻¹ * h⁻¹) * (h * g) * u` using `by group`. Use `show h * (u⁻¹ * g * u) ∈ L.KN N ↔ h * g ∈ L.KN N`.

Rewrite using `[e, Subgroup.mul_mem_cancel_right _ b, Subgroup.mul_mem_cancel_left _ a]`.
-/
private theorem s_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ} {h : G.GAf}
    (hd : N ∣ N') (hc : ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N) :
    ∀ u ∈ L.KN N', ∀ g, u⁻¹ * g * u ∈ {g | h * g ∈ L.KN N} ↔ g ∈ {g | h * g ∈ L.KN N} := by
  intro u hu g
  have a : h * u⁻¹ * h⁻¹ ∈ L.KN N := hc _ (inv_mem hu)
  have b : u ∈ L.KN N := kn_anti L hd hu
  have e : h * (u⁻¹ * g * u) = (h * u⁻¹ * h⁻¹) * (h * g) * u := by group
  show h * (u⁻¹ * g * u) ∈ L.KN N ↔ h * g ∈ L.KN N
  rw [e, Subgroup.mul_mem_cancel_right _ b, Subgroup.mul_mem_cancel_left _ a]

/- English proof (translation)
Take `⟨⟨c, hc⟩, hS, hK⟩` from `H`. Take `⟨⟨c', hc'⟩, hS', hK'⟩` from `H'`. Establish `hS1 : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ K` using `hS`. Establish `hS2 : h * (a.1.1⁻¹ * B.toAf y' * a.1.1) ∈ K` using `hS'`. Use `⟨⟨c⁻¹ * c', ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ w : Fin G.n → ℂ, ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ ((LKCx.toV G v B.β y).val *ᵥ w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[map_mul, map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]`. Distinguish the cases in `h0 : c = 0`.

Establish `hz` using `key a.2.1`. Rewrite `hz` using `[hc, h0, zero_smul, Matrix.mulVec_zero]`. Rewrite using `[← hz]`. Simplify using the standard rewrite rules. Establish `hz` using `key a.2.1`.

Rewrite `hz` using `[hc, Matrix.mulVec_smul]`. Establish `h3 : ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1 = c⁻¹ • a.2.1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, _root_.inv_mul_cancel₀ h0, one_smul]`. Use `_ = _ := by rw [hz]`.

Rewrite using `[h3, smul_smul, _root_.mul_comm]`. Use `show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K`. Establish `e : a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 = (h * (a.1.1⁻¹ * B.toAf y * a.1.1))⁻¹ * (h * (a.1.1⁻¹ * B.toAf y' * a.1.1))`. Rewrite using `[map_mul, map_inv]`. Use `group`.

Rewrite using `[e]`. Conclude with `K.mul_mem (K.inv_mem hS1) hS2`. Establish `e : a.1.2⁻¹ * LKCx.toP1 G B.β (y⁻¹ * y') * a.1.2 = (a.1.2⁻¹ * LKCx.toP1 G B.β y * a.1.2)⁻¹ * (a.1.2⁻¹ * LKCx.toP1 G B.β y' * a.1.2)`. Rewrite using `[map_mul, map_inv]`. Use `group`.

Rewrite using `[e]`. Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ hK) hK'`.
-/
private theorem sees_div {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (a : GlobalTheory.LKCx.Dat G v B.β) (K : Subgroup G.GAf) (h : G.GAf) (y y' : GlobalTheory.LKCx.grp G B.β)
    (H : Sees B {g | h * g ∈ K} a y) (H' : Sees B {g | h * g ∈ K} a y') : Sees B (K : Set G.GAf) a (y⁻¹ * y') := by
  obtain ⟨⟨c, hc⟩, hS, hK⟩ := H
  obtain ⟨⟨c', hc'⟩, hS', hK'⟩ := H'
  have hS1 : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ K := hS
  have hS2 : h * (a.1.1⁻¹ * B.toAf y' * a.1.1) ∈ K := hS'
  refine ⟨⟨c⁻¹ * c', ?_⟩, ?_, ?_⟩
  · have key : ∀ w : Fin G.n → ℂ,
        ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ ((LKCx.toV G v B.β y).val *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [map_mul, map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
    by_cases h0 : c = 0
    · have hz := key a.2.1
      rw [hc, h0, zero_smul, Matrix.mulVec_zero] at hz
      rw [← hz]
      simp
    · have hz := key a.2.1
      rw [hc, Matrix.mulVec_smul] at hz
      have h3 : ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1 = c⁻¹ • a.2.1 := by
        calc _ = c⁻¹ • (c • (((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1)) := by
                rw [smul_smul, _root_.inv_mul_cancel₀ h0, one_smul]
          _ = _ := by rw [hz]
      rw [h3, smul_smul, _root_.mul_comm]
  · show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K
    have e : a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 =
        (h * (a.1.1⁻¹ * B.toAf y * a.1.1))⁻¹ * (h * (a.1.1⁻¹ * B.toAf y' * a.1.1)) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact K.mul_mem (K.inv_mem hS1) hS2
  · have e : a.1.2⁻¹ * LKCx.toP1 G B.β (y⁻¹ * y') * a.1.2 =
        (a.1.2⁻¹ * LKCx.toP1 G B.β y * a.1.2)⁻¹ * (a.1.2⁻¹ * LKCx.toP1 G B.β y' * a.1.2) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hK) hK'

/- English proof (translation)
Introduce `hRS hGU hPDE hRDE hUG hST hFF hFE hFG hFLo hTE hFFin hPS hPO hSP hES`. Introduce `p _ D G L ha hm v hs t₀ ht gb hstd N N' h hlev X X' c₁ c₂ hreg k α hα het h₁ h₂`. Take `⟨h3, hcp, h3', hcp', hd, hconj⟩` from `hlev`. Take `⟨ρ, hsig⟩` from `hRS p D ha hm t₀ ht`. Take `⟨hsm, hqc, hsep, hX, hL, hfine, ⟨U₀⟩⟩` from `hGU p D ha hm t₀ ht ρ hsig gb hstd N h3 hcp X`.

Take `⟨hsm', hqc', hsep', hX', hL', hfine', ⟨U⟩⟩` from `hGU p D ha hm t₀ ht ρ hsig gb hstd N' h3' hcp' X'`. Establish `hpow` using `@hPS X.X X.s (D.n - 1) D.g hsm hqc hsep X.univ.A X.univ.grp X.univ.comm X.univ.ab hX k`. Establish `hpow'` using `@hPS X'.X X'.s (D.n - 1) D.g hsm' hqc' hsep' X'.univ.A X'.univ.grp X'.univ.comm X'.univ.ab hX' k`. Use `⟨hpow.1, ?_⟩` and prove the remaining obligations. Establish `hTan : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → ∃ A, W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x A` using `fun x hx => hTE _ _ (sZ X k) (sZ X' k) _ hpow.1 (c₁.pw k) (c₂.tw α) h₁ h₂ het x hx`.

Set `At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ` to `fun x => if hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α then (hTan x hx).choose else 0`. Establish `hAt : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), ∀ hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α, W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x)`. Introduce `x hx`. Simplify using `only [At, dif_pos hx]`. Conclude with `(hTan x hx).choose_spec`.

Set `PD : (B : LKCx.Form G) → PDic L B.β` to `fun B => (hPDE p D G L ha hm B).some`. Set `RD : (B : LKCx.Form G) → RDic L v B.β ρ t₀` to `fun B => (hRDE p D G L ha hm v hs t₀ ht ρ hsig B).some`. Take `⟨Φ, hΦ⟩` from `hUG p D G L ha hm v hs t₀ ht ρ hsig PD RD N' (by omega) hcp' _ U`. Establish `hproj : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ X'.s = spMap (RingHom.id ℂ)`. Introduce `x`.

Rewrite using `[Category.assoc]`. Conclude with `x.2`. Set `π : CxPts (sZ X' k) (RingHom.id ℂ) → CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ)` to `fun x => ⟨x.1 ≫ (KS.pow X'.univ.A k).hom, hproj x⟩`. Establish `hbase : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₁.q = (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₂.q`. Introduce `x hx`.

Rewrite using `[Category.assoc, Category.assoc, ← (hPO p D G L gb N N' 1 X X' c₁ k).1, ← ((hPO p D G L gb N N' h X X' c₂ k).2.2.2 α).1, ← Category.assoc, ← Category.assoc, hx]`. Establish `hFwd : ∀ (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j, PELU.IsPeriod (U.Di i) ρ P → IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a → U.u i P ≫ c₁.q = U.u i P ≫ c₂.q → ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y` using `fun q a i P j hper hco hfb => hFF p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ (Quot.out q) (PD _) (RD _) (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P) (U.unif i P hper) hfb`. Establish `hLoc` using `fun (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j (hper : PELU.IsPeriod (U.Di i) ρ P) (hco : IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a) (y : LKCx.grp G (Quot.out q).β) (hy : Sees (Quot.out q) {g | h * g ∈ L.KN N} …`. Establish `hdet : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → (1 - At x).det ≠ 0`. Introduce `x hx`.

Take `⟨q, a, i, P, j, -, hper, hxu, hco⟩` from `hΦ (π x)`. Establish `hxu' : x.1 ≫ (KS.pow X'.univ.A k).hom = U.u i P` using `hxu`. Establish `hfb : U.u i P ≫ c₁.q = U.u i P ≫ c₂.q` using `by rw [← hxu']; exact hbase x hx`. Take `⟨y, hy⟩` from `hFwd q a i P j hper hco hfb`. Take `⟨Fl, hFl, -, hAll⟩` from `hLoc q a i P j hper hco y hy`.

Conclude with `(hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).1 x ((hFl x).2 ⟨hxu', hx⟩)`. Establish `hfin : {x : CxPts (sZ X' k) (RingHom.id ℂ) | x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α}.Finite` using `hFFin _ _ (sZ X k) (sZ X' k) (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ hpow.2.2.1 hpow'.2.1 hpow'.2.2.2 (fun x hx => ⟨At x, hAt x hx, hdet x hx⟩)`. Establish `hSinv` using `s_inv L hd hconj`. Establish `hK1 : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y : LKCx.grp G B.β), Sees B (L.KN N' : Set G.GAf) a y → y = 1` using `fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N' h3' hcp' B a y hy`. Establish `huniq : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y y' : LKCx.grp G B.β), Sees B {g | h * g ∈ L.KN N} a y → Sees B {g | h * g ∈ L.KN N} a y' → y = y'`.

Introduce `B a y y' hy hy'`. Conclude with `_root_.inv_mul_eq_one.1 (hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a _ (sees_div B a (L.KN N) h y y' hy hy'))`. Establish `hFb : ∀ (x' : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ)) (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j, PELU.IsPeriod (U.Di i) ρ P → x'.1 = U.u i P → IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a → (x' ∈ hfin.toFi …`. Introduce `x' q a i P j hper hxu hco`. Prove the components needed by the constructor for the conclusion.

Introduce `hx'`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hx'`. Establish `hx2 : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α` using `hfin.mem_toFinset.1 hx`. Apply `hFwd q a i P j hper hco` to reduce the goal to its premises. Rewrite using `[← hxu]`.

Conclude with `hbase x hx2`. Introduce and unpack `⟨y, hy⟩`. Take `⟨Fl, hFl, ⟨x, hxF⟩, -⟩` from `hLoc q a i P j hper hco y hy`. Take `⟨hxu', hx2⟩` from `(hFl x).1 hxF`. Conclude with `Finset.mem_image.2 ⟨x, hfin.mem_toFinset.2 hx2, Subtype.ext (hxu'.trans hxu.symm)⟩`.

Use `⟨hfin.toFinset, At, fun x => by rw [Set.Finite.mem_toFinset]; rfl, fun x hx => ⟨hAt x (hfin.mem_toFinset.1 hx), hdet x (hfin.mem_toFinset.1 hx)⟩, ?_, fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a y hy, fun t => ?_⟩` and prove the remaining obligations. Use `((hfin.toFinset.image π).finite_toSet.image Φ).subset ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩` from `hΦ (Φ.symm z)`. Rewrite `hΦx` using `[Equiv.apply_symm_apply]`.

Substitute `hΦx` using the available equality. Use `⟨Φ.symm _, ?_, Equiv.apply_symm_apply _ _⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hz`. Take `⟨E, -, hE⟩` from `hES p G v (fun _ _ => 0) (Quot.out q) (L.KN N') {g | h * g ∈ L.KN N} hSinv _ a (Quot.out_eq _)`. Conclude with `(hFb _ q a i P j hper hxu hco).2 ⟨E y, (hE y).1.1 hy⟩`.

Set `w : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) → ℂ` to `fun x' => ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t`. Establish `hsum : ∑ x ∈ hfin.toFinset, lefTerm (At x) t = ∑ x' ∈ hfin.toFinset.image π, w x'` using `(Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm`. Rewrite using `[hsum]`. Use `hSP p G v (wtFix L v t₀ α t) (L.KN N') {g | h * g ∈ L.KN N} hSinv hK1 huniq _ Φ _ w (fun x' => ?_)` and prove the remaining obligations. Take `⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩` from `hΦ x'`.

Use `⟨q, a, hΦx, hFb x' q a i P j hper hxu hco, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨Fl, hFl, -, hAll⟩` from `hLoc q a i P j hper hco y hy`. Establish `hEq : hfin.toFinset.filter (fun x => π x = x') = Fl`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hFl x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, he⟩`. Use `⟨?_, hx⟩` and prove the remaining obligations. Rewrite using `[← hxu, ← he]`. Both sides reduce to the same expression.

Introduce and unpack `⟨he, hx⟩`. Conclude with `⟨hx, Subtype.ext (he.trans hxu.symm)⟩`. Use `show ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t = _`. Rewrite using `[hEq]`. Conclude with `(hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).2 t`.
-/
theorem UpperTheory.Gal.W2.fixedPoints_integral_base_of_uniformisation :
    UpperTheory.Gal.W2.RhoSig → UpperTheory.Gal.W2.GUnif → UpperTheory.Gal.W2.PDicEx → UpperTheory.Gal.W2.RDicEx → UpperTheory.Gal.W2.UnifG → UpperTheory.Gal.W2.StabTriv → UpperTheory.Gal.W2.FixFwd → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixLoc → UpperTheory.Gal.W2.TanExists → UpperTheory.Gal.W2.FixFinite → UpperTheory.Gal.W2.PowSm → UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.SumPts → UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.HeckeFixedPointCMCycleClass := by
  intro hRS hGU hPDE hRDE hUG hST hFF hFE hFG hFLo hTE hFFin hPS hPO hSP hES
  intro p _ D G L ha hm v hs t₀ ht gb hstd N N' h hlev X X' c₁ c₂ hreg k α hα het h₁ h₂
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨ρ, hsig⟩ := hRS p D ha hm t₀ ht
  obtain ⟨hsm, hqc, hsep, hX, hL, hfine, ⟨U₀⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N h3 hcp X
  obtain ⟨hsm', hqc', hsep', hX', hL', hfine', ⟨U⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N' h3' hcp' X'
  have hpow := @hPS X.X X.s (D.n - 1) D.g hsm hqc hsep X.univ.A X.univ.grp X.univ.comm X.univ.ab hX k
  have hpow' := @hPS X'.X X'.s (D.n - 1) D.g hsm' hqc' hsep' X'.univ.A X'.univ.grp X'.univ.comm X'.univ.ab hX' k
  refine ⟨hpow.1, ?_⟩
  have hTan : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      ∃ A, W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x A :=
    fun x hx => hTE _ _ (sZ X k) (sZ X' k) _ hpow.1 (c₁.pw k) (c₂.tw α) h₁ h₂ het x hx
  let At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ :=
    fun x => if hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α then (hTan x hx).choose else 0
  have hAt : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), ∀ hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α,
      W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) := by
    intro x hx
    simp only [At, dif_pos hx]
    exact (hTan x hx).choose_spec
  let PD : (B : LKCx.Form G) → PDic L B.β := fun B => (hPDE p D G L ha hm B).some
  let RD : (B : LKCx.Form G) → RDic L v B.β ρ t₀ := fun B => (hRDE p D G L ha hm v hs t₀ ht ρ hsig B).some
  obtain ⟨Φ, hΦ⟩ := hUG p D G L ha hm v hs t₀ ht ρ hsig PD RD N' (by omega) hcp' _ U
  have hproj : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ),
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ X'.s = spMap (RingHom.id ℂ) := by
    intro x
    rw [Category.assoc]
    exact x.2
  let π : CxPts (sZ X' k) (RingHom.id ℂ) → CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) :=
    fun x => ⟨x.1 ≫ (KS.pow X'.univ.A k).hom, hproj x⟩
  have hbase : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₁.q = (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₂.q := by
    intro x hx
    rw [Category.assoc, Category.assoc, ← (hPO p D G L gb N N' 1 X X' c₁ k).1,
      ← ((hPO p D G L gb N N' h X X' c₂ k).2.2.2 α).1, ← Category.assoc, ← Category.assoc, hx]
  have hFwd : ∀ (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      U.u i P ≫ c₁.q = U.u i P ≫ c₂.q → ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y :=
    fun q a i P j hper hco hfb => hFF p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ
      hfine v t₀ (Quot.out q) (PD _) (RD _) (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P)
      (U.unif i P hper) hfb
  have hLoc := fun (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j
      (hper : PELU.IsPeriod (U.Di i) ρ P)
      (hco : IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a)
      (y : LKCx.grp G (Quot.out q).β) (hy : Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) =>
    hFLo p D G L ha hm v hs t₀ ht gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig
      hsm' hreg U (Quot.out q) (PD _) (RD _) i P j a hper hco y hy k α hα h₁ h₂
  have hdet : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → (1 - At x).det ≠ 0 := by
    intro x hx
    obtain ⟨q, a, i, P, j, -, hper, hxu, hco⟩ := hΦ (π x)
    have hxu' : x.1 ≫ (KS.pow X'.univ.A k).hom = U.u i P := hxu
    have hfb : U.u i P ≫ c₁.q = U.u i P ≫ c₂.q := by rw [← hxu']; exact hbase x hx
    obtain ⟨y, hy⟩ := hFwd q a i P j hper hco hfb
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).1 x ((hFl x).2 ⟨hxu', hx⟩)
  have hfin : {x : CxPts (sZ X' k) (RingHom.id ℂ) | x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α}.Finite :=
    hFFin _ _ (sZ X k) (sZ X' k) (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ hpow.2.2.1 hpow'.2.1 hpow'.2.2.2
      (fun x hx => ⟨At x, hAt x hx, hdet x hx⟩)
  have hSinv := s_inv L hd hconj
  have hK1 : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y : LKCx.grp G B.β),
      Sees B (L.KN N' : Set G.GAf) a y → y = 1 :=
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N' h3' hcp' B a y hy
  have huniq : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y y' : LKCx.grp G B.β),
      Sees B {g | h * g ∈ L.KN N} a y → Sees B {g | h * g ∈ L.KN N} a y' → y = y' := by
    intro B a y y' hy hy'
    exact _root_.inv_mul_eq_one.1
      (hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a _ (sees_div B a (L.KN N) h y y' hy hy'))
  have hFb : ∀ (x' : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ)) (q : LKCx.FCls G)
      (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P → x'.1 = U.u i P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      (x' ∈ hfin.toFinset.image π ↔ ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) := by
    intro x' q a i P j hper hxu hco
    constructor
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      have hx2 : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α := hfin.mem_toFinset.1 hx
      apply hFwd q a i P j hper hco
      rw [← hxu]
      exact hbase x hx2
    · rintro ⟨y, hy⟩
      obtain ⟨Fl, hFl, ⟨x, hxF⟩, -⟩ := hLoc q a i P j hper hco y hy
      obtain ⟨hxu', hx2⟩ := (hFl x).1 hxF
      exact Finset.mem_image.2 ⟨x, hfin.mem_toFinset.2 hx2, Subtype.ext (hxu'.trans hxu.symm)⟩
  refine ⟨hfin.toFinset, At, fun x => by rw [Set.Finite.mem_toFinset]; rfl,
    fun x hx => ⟨hAt x (hfin.mem_toFinset.1 hx), hdet x (hfin.mem_toFinset.1 hx)⟩, ?_,
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a y hy, fun t => ?_⟩
  · refine ((hfin.toFinset.image π).finite_toSet.image Φ).subset ?_
    intro z hz
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ (Φ.symm z)
    rw [Equiv.apply_symm_apply] at hΦx
    subst hΦx
    refine ⟨Φ.symm _, ?_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨y, hy⟩ := hz
    obtain ⟨E, -, hE⟩ := hES p G v (fun _ _ => 0) (Quot.out q) (L.KN N') {g | h * g ∈ L.KN N} hSinv _ a
      (Quot.out_eq _)
    exact (hFb _ q a i P j hper hxu hco).2 ⟨E y, (hE y).1.1 hy⟩
  · let w : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) → ℂ :=
      fun x' => ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t
    have hsum : ∑ x ∈ hfin.toFinset, lefTerm (At x) t = ∑ x' ∈ hfin.toFinset.image π, w x' :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm
    rw [hsum]
    refine hSP p G v (wtFix L v t₀ α t) (L.KN N') {g | h * g ∈ L.KN N} hSinv hK1 huniq _ Φ _ w (fun x' => ?_)
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ x'
    refine ⟨q, a, hΦx, hFb x' q a i P j hper hxu hco, fun y hy => ?_⟩
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    have hEq : hfin.toFinset.filter (fun x => π x = x') = Fl := by
      ext x
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hFl x]
      constructor
      · rintro ⟨hx, he⟩
        refine ⟨?_, hx⟩
        rw [← hxu, ← he]
        rfl
      · rintro ⟨he, hx⟩
        exact ⟨hx, Subtype.ext (he.trans hxu.symm)⟩
    show ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t = _
    rw [hEq]
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).2 t
