import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDownStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelOfFullStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMoveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLimitPointTateIsoSequenceStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

/- English proof (translation)
Use `⟨H.1, H.2.1, fun p => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩` from `H.2.2 p`. Conclude with `⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4, fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩`.
-/
theorem isThetaPt_comp {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) : IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `H`. Use `⟨h1, h2, fun p => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩` from `h3 p`. Take `⟨c', hc'⟩` from `hc.map V.ι.appTop.hom`. Use `⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩` and prove the remaining obligations.

Establish `aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)), V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀`. Introduce `a u₀ w₀ h`. Rewrite using `[map_mul, h, Units.val_mul, hc', _root_.mul_assoc]`. Conclude with `aux (v i) u (w i) (a8 i)`.
-/
theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Use `I.add M 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `left_eq_mul.1 this`. Consider the case `succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]`.
-/
theorem ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) (M r : ℕ) (a : D.La) : I.ev M (r • a) = I.ev M a ^ r := by
  induction r with
  | zero =>
    have := I.add M 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]

/- English proof (translation)
Establish `e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a` using `fun a => by`. Rewrite using `[ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h₁` using `GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul hL K o.P r m D.La _ _ (fun a => by`.

Rewrite using `[e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)`. Establish `h₂` using `isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁`. Simplify using `only [e] at h₂`. Unfold `Full.Theta`. Use `h₂ using 2 with a` and compare the differences between its conclusion and the goal.

Rewrite using `[hc]`. Conclude with `(congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)`.
-/
theorem theta_down (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] (o : Full D K) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {v v' : D.La → K} (c : Kˣ) (hc : ∀ x, v (r • x) = c * v' x) (h : o.Theta (r * m) v) : o.Theta m v' := by
  have e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a := fun a => by
    rw [ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]
    congr 2; ring
  have h₁ := GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul hL K o.P r m D.La _ _ (fun a => by
    rw [e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)
  have h₂ := isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁
  simp only [e] at h₂
  unfold Full.Theta
  convert h₂ using 2 with a
  rw [hc]
  exact (congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)

/- English proof (translation)
Use `letI := H.starRing`. Take `⟨bas, hbas⟩` from `GlobalTheory.ZM.exists_isSympBasis E H D`. Generalize the expression as in `Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas`. Use `choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)`. Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)`.

Set `B` to `((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)`. Use `⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, J = j + 4` from `⟨J - 4, by omega⟩`. Establish `hB : B < n ^ (j + 4)` using `lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)`. Establish `hp : 0 < n ^ (j + 4)` using `pow_pos hn.pos _`.

Use `set M := (n ^ (j + 4)) ^ 2 with hM`. Establish `hM0 : 0 < M` using `pow_pos hp _`. Use `haveI : NeZero M := ⟨hM0.ne'⟩`. Use `haveI := o.charZero`. Take `⟨hg, lev, hb, hl⟩` from `GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o M hM0`.

Establish `Q` using `GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o' M hM0`. Rewrite `Q` using `[← hζ]`. Take `⟨hg', lev', hb', hl'⟩` from `Q`. Set `lab : (Fin (2 * g) → ZMod M) → D.La` to `fun a => bas fun i => ((a i).val : ℤ)`. Establish `hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a` using `fun a => funext fun i => by simp`.

Establish `e : levelPoint lev hg = fun a => o.I.ev M (lab a)` using `funext fun a => by rw [← hl, hlab]`. Establish `e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a)` using `funext fun a => by rw [← hl', hlab]`. Establish `key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2` using `fun c hc =>`. Combine the equalities or inequalities in the displayed calculation. Take `⟨φ, hφ, hφb⟩` from `h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a))) (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)`.

Use `haveI := hφ.1`. Establish `hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a` using `fun a => by`. Take `⟨c, rfl⟩` from `bas.surjective a`. Rewrite using `[← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]`. Conclude with `congrArg (linComb · _) (funext hφb)`.

Use `⟨φ, hφ, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E))` using `hs ▸ Submodule.mem_top`. Establish `add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b` using `o.oa.map_add`. Establish `add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b` using `o'.oa.map_add`. Set `f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom)) fun a b => by rw [add, MonObj.mul_comp]; rfl`.

Set `f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a)) fun a b => by rw [add', MonObj.comp_mul]; rfl`. Establish `: f = f'` using `AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E))) (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by`. Use `congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg' φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)` and prove the remaining obligations. Take `⟨b, rfl⟩` from `(o.I.onto M hM0 y).1 hy`. Establish `l` using `o.I.lin M a b`.

Establish `l'` using `o'.I.lin M a b`. Rewrite using `[← Category.assoc, ← Category.assoc, ← l, hev, hev, l']`. Conclude with `Additive.ofMul.injective (DFunLike.congr_fun this x)`.
-/
theorem exists_iso (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) (D : Datum H) {n : ℕ}
    (hn : n.Prime) (ho : Odd n) : ∃ J₀, ∀ J, J₀ ≤ J → ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (v : D.La → K),
      o.I.ζ ((n ^ J) ^ 2) = o'.I.ζ ((n ^ J) ^ 2) → o.Theta (n ^ J) v → o'.Theta (n ^ J) v →
      ∃ φ : o.P.A ≅ o'.P.A, IsPolIso o.P o'.P φ ∧
        (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) := by
  letI := H.starRing
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  generalize Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas
  choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  let B := ((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)
  refine ⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : B < n ^ (j + 4) := lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hp : 0 < n ^ (j + 4) := pow_pos hn.pos _
  set M := (n ^ (j + 4)) ^ 2 with hM
  have hM0 : 0 < M := pow_pos hp _
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI := o.charZero
  obtain ⟨hg, lev, hb, hl⟩ := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o M hM0
  have Q := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o' M hM0
  rw [← hζ] at Q
  obtain ⟨hg', lev', hb', hl'⟩ := Q
  let lab : (Fin (2 * g) → ZMod M) → D.La := fun a => bas fun i => ((a i).val : ℤ)
  have hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a := fun a => funext fun i => by simp
  have e : levelPoint lev hg = fun a => o.I.ev M (lab a) := funext fun a => by rw [← hl, hlab]
  have e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a) := funext fun a => by rw [← hl', hlab]
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ B := le_add_left (by gcongr)
      _ < n ^ (j + 4) := hB
      _ ≤ M := Nat.le_self_pow two_ne_zero _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨φ, hφ, hφb⟩ := h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K
    (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a)))
    (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)
  haveI := hφ.1
  have hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a := fun a => by
    obtain ⟨c, rfl⟩ := bas.surjective a
    rw [← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (linComb · _) (funext hφb)
  refine ⟨φ, hφ, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E)) := hs ▸ Submodule.mem_top
  have add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b := o.oa.map_add
  have add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b := o'.oa.map_add
  let f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom))
    fun a b => by rw [add, MonObj.mul_comp]; rfl
  let f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a))
    fun a b => by rw [add', MonObj.comp_mul]; rfl
  have : f = f' := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by
    refine congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg'
      φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)
    obtain ⟨b, rfl⟩ := (o.I.onto M hM0 y).1 hy
    have l := o.I.lin M a b
    have l' := o'.I.lin M a b
    rw [← Category.assoc, ← Category.assoc, ← l, hev, hev, l']
  exact Additive.ofMul.injective (DFunLike.congr_fun this x)

/- English proof (translation)
Take `⟨J, hJ⟩` from `exists_iso hL h₁ h₂ D hn ho`. Use `choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)`. Establish `hp : ∀ i, 0 < n ^ i` using `fun i => pow_pos hn.pos i`. Establish `th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i))` using `fun j i hi => by`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le' hi`.

Take `⟨c, hc⟩` from `hv (n ^ d) (n ^ i) ho.pow ho.pow`. Use `theta_down hL (o j) (hp d) (hp i) c hc ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← hd]`. Conclude with `ht j`. Establish `ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i)` using `fun j i hi => by`.

Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hi`. Use `hz j` as an intermediate fact. Rewrite `this` using `[← pow_mul, mul_comm, hd, pow_add]`. Rewrite using `[← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]`. Establish `ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2)` using `fun j i hi => by`.

Rewrite using `[← pow_mul]; exact ze j _ (by omega)`. Use `choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _ ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)`. Use `choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)`. Take `⟨I', hI'⟩` from `GlobalTheory.T.exists_limitPoint_tateIso_sequence E H D K _ _ _ I`. Use `⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Take `⟨j, hj, -, e⟩` from `hI' _ (hp i) i`. Conclude with `e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))`. Take `⟨j, hj, e, -⟩` from `hI' _ (pow_pos (hp i) 2) i`. Use `hI j _ _ (th j i (by omega))` as an intermediate fact. Unfold `Full.Theta at this ⊢`.

Simplify using `only at this ⊢`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem exists_full_all (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) {K : Type} [Field K]
    [IsAlgClosed K] (ρ : K) (ζ : ℕ → Kˣ) (hζ : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (v : ℕ → D.La → K)
    (hv : ∀ r m, Odd r → Odd m → ∃ c : Kˣ, ∀ x, v (r * m) (r • x) = c * v m x) {n : ℕ} (hn : n.Prime) (ho : Odd n)
    (h : ∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = ρ ∧ o.I.ζ ((n ^ j) ^ 2) = ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (v (n ^ j))) :
    ∃ o : Full D K, o.ρ = ρ ∧ ∀ j, o.I.ζ (n ^ j) = ζ (n ^ j) ∧ o.Theta (n ^ j) (v (n ^ j)) := by
  obtain ⟨J, hJ⟩ := exists_iso hL h₁ h₂ D hn ho
  choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)
  have hp : ∀ i, 0 < n ^ i := fun i => pow_pos hn.pos i
  have th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i)) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨c, hc⟩ := hv (n ^ d) (n ^ i) ho.pow ho.pow
    refine theta_down hL (o j) (hp d) (hp i) c hc ?_
    rw [← pow_add, ← hd]; exact ht j
  have ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have := hz j
    rw [← pow_mul, mul_comm, hd, pow_add] at this
    rw [← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]
  have ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2) := fun j i hi => by
    rw [← pow_mul]; exact ze j _ (by omega)
  choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _
    ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)
  choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)
  obtain ⟨I', hI'⟩ := GlobalTheory.T.exists_limitPoint_tateIso_sequence E H D K _ _ _ I
  refine ⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, -, e⟩ := hI' _ (hp i) i
    exact e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))
  · obtain ⟨j, hj, e, -⟩ := hI' _ (pow_pos (hp i) 2) i
    have := hI j _ _ (th j i (by omega))
    unfold Full.Theta at this ⊢
    dsimp only at this ⊢
    rw [e]; exact this

end GlobalTheory.Ex.AllLevels
