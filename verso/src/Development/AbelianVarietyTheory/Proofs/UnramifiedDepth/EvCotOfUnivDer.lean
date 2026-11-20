import Mathlib
import ReciprocityTheory.DualLattices.EvCotStatement

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

namespace CotOf

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

variable (D : Dat p g B Tw Dt Oe σ cp)

section
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]

end

/- English proof (translation)
Rewrite using `[ZMod.val_natCast]`. Use `conv_rhs => rw [← Nat.mod_add_div n p, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]`.
-/
lemma val_smul {G : Type} [AddCommGroup G] (x : G) (hx : p • x = 0) (n : ℕ) :
    (n : ZMod p).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]

end CotOf

open TensorProduct IsLocalRing Matrix in

/- English proof (translation)
Introduce `hU R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D`. Unfold `_root_.ReciprocityTheory.PGsh.Be2.EvCotStatement`. Introduce `C _ _ hinj`. Use `letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i => ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra`. Establish `hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧ B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t` using `fun t => by`.

Establish `h` using `(D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec`. Conclude with `⟨h.1, h.2.1⟩`. Establish `hsec : ∀ t c, (D.ptMap t).1 ((D.fin.sO (D.ptIdx t)).1 c) = c` using `fun t c => congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 c) (hspec t).1`. Set `ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier` to `fun t => { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp (Pi.evalRingHom _ (D.ptIdx t)) commutes' := fun o => hsec t o }`. Set `Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier)` to `Pi.algHom _ _ ev`.

Set `f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C)` to `(Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap`. Establish `hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x)))` using `fun F x => rfl`. Establish `hfmul : ∀ F G, f (F * G) = f F * f G` using `fun F G => by`. Use function extensionality and compare the values at `x`. Simplify using `only [hf, Pi.mul_apply, map_mul]`.

Establish `himg : D.evImg C = LinearMap.range f`. Unfold `_root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll`. Express the relevant statement in the definitionally equal form `Submodule.span _ (Set.range ⇑f) = _`. Rewrite using `[← LinearMap.coe_range, Submodule.span_eq]`. Establish `hinjΨ : Function.Injective Ψ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `F hF`. Use function extensionality and compare the values at `i`. Apply `D.fin.sep i` to reduce the goal to its premises. Introduce `φ hφ`.

Establish `hz : p • B.map φ (D.fin.y i) = 0` using `by rw [← map_nsmul, D.fin.y_p, map_zero]`. Take `⟨t, ht⟩` from `D.L.τ_basis.2 ⟨_, hz⟩`. Establish `ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i)` using `congrArg Subtype.val ht`. Take `⟨i0, φ0, -, -, huniq⟩` from `D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz`. Take `⟨hi, hφ0⟩` from `huniq i φ hφ rfl`.

Take `⟨hi', hψ0⟩` from `huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')`. Substitute `hi` using the available equality. Establish `key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ → ψ.1 (F j) = φ.1 (F i)`. Introduce and unpack `j ψ rfl h`. Rewrite using `[eq_of_heq h]`.

Conclude with `(key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)`. Establish `finj : Function.Injective f` using `fun F G h => hinjΨ (funext fun x => hinj (congrFun h x))`. Take `⟨δ, hδlin, hδder, hδuniv, hδeq⟩` from `hU D`. Use `clear hU`. Establish `hπs : ∀ c, (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c) = c` using `hsec 0`.

Establish `hδ1 : δ 1 = 0`. Establish `h` using `hδder 1 1`. Simplify using `only [mul_one, map_one, one_smul] at h`. Establish `h2 : δ 1 + δ 1 = δ 1 + 0` using `by rw [add_zero]; exact h.symm`. Conclude with `add_left_cancel h2`.

Establish `hδs : ∀ c, δ ((D.fin.sO (D.ptIdx 0)).1 c) = 0` using `fun c => by`. Establish `h` using `hδlin c 1`. Rewrite `h` using `[mul_one, hδ1, smul_zero]`. Conclude with `h`. Establish `hδsurj : Function.Surjective δ`.

Set `N : Submodule Tw.O.carrier (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g)` to `{ carrier := Set.range δ add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add δ x y⟩ zero_mem' := ⟨0, map_zero δ⟩ smul_mem' := by rintro c _ ⟨x, rfl⟩; exact ⟨_, hδlin c x⟩ }`. Set `d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g ⧸ N)` to `N.mkQ.toAddMonoidHom.comp δ`. Take `⟨u, -, huniq⟩` from `hδuniv _ d (fun o x => by simp only [d, AddMonoidHom.comp_apply, hδlin]; exact map_smul N.mkQ o (δ x)) (fun x y => by`. Simplify using `only [d, AddMonoidHom.comp_apply, hδder]`. Conclude with `(map_add N.mkQ _ _).trans (by rw [map_smul, map_smul]; rfl))`.

Establish `h1` using `huniq N.mkQ (fun x => rfl)`. Establish `h2` using `huniq 0 (fun x => by show N.mkQ (δ x) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨x, rfl⟩)`. Introduce `q`.

Establish `hq : N.mkQ q = 0` using `by rw [h1.trans h2.symm]; rfl`. Rewrite `hq` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hq`. Establish `hmemA : ∀ F, f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ↔ (D.ptMap 0).1 (F (D.ptIdx 0)) = 0` using `fun F => by`. Unfold `_root_.ReciprocityTheory.PGsh.L2.augIdeal`.

Rewrite using `[Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply, hf]`. Use `⟨fun h => hinj (h.2.trans (map_zero _).symm), fun h => ⟨?_, by rw [h, map_zero]⟩⟩` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `⟨F, rfl⟩`. Establish `hle : _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ≤ LinearMap.range f` using `fun h hh => by`.

Unfold `_root_.ReciprocityTheory.PGsh.L2.augIdeal at hh`. Rewrite using `[← himg]`. Conclude with `(Submodule.mem_inf.1 hh).1`. Set `e` to `LinearEquiv.ofInjective f finj`. Set `Δ : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] _root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g` to `{ toFun := fun F => δ (F (D.ptIdx 0)) map_add' := fun F G => map_add δ _ _ map_smul' := fun c F => hδlin c _ }`.

Set `φ` to `Δ ∘ₗ (e.symm : LinearMap.range f →ₗ[Tw.O.carrier] _) ∘ₗ Submodule.inclusion hle`. Establish `hφ : ∀ F (hF : f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), φ ⟨f F, hF⟩ = δ (F (D.ptIdx 0))` using `fun F hF => by`. Establish `he : e.symm ⟨f F, hle hF⟩ = F` using `e.symm_apply_eq.2 (Subtype.ext (by simp [e]))`. Use `show Δ (e.symm ⟨f F, hle hF⟩) = _`. Rewrite using `[he]`.

Both sides reduce to the same expression. Use `⟨φ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨x, rfl⟩` from `hδsurj q`. Establish `hx' : (D.ptMap 0).1 (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) = 0`.

Rewrite using `[map_sub, hπs, sub_self]`. Establish `hmem : f (Pi.single (D.ptIdx 0) (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)` using `(hmemA _).2 (by rw [Pi.single_eq_same]; exact hx')`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, Pi.single_eq_same, map_sub, hδs, sub_zero]`. Use extensionality with `⟨h, hh⟩`.

Rewrite using `[LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]`. Take `⟨F, rfl⟩ : h ∈ LinearMap.range f` from `hle hh`. Rewrite using `[hφ F hh]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Set `π0 : (D.fin.AAx (D.ptIdx 0)).carrier →ₗ[Tw.O.carrier] Tw.O.carrier` to `{ toFun := (D.ptMap 0).1 map_add' := map_add _ map_smul' := fun c x => by show (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c * x) = c * (D.ptMap 0).1 x`. Rewrite using `[map_mul, hπs] }`. Set `I` to `LinearMap.ker π0`. Set `J : Submodule Tw.O.carrier I` to `Submodule.comap I.subtype (Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b})`. Establish `hsub : ∀ x, x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) ∈ I` using `fun x => by`.

Rewrite using `[LinearMap.mem_ker]`. Use `show (D.ptMap 0).1 (x - _) = 0`. Rewrite using `[map_sub, hπs, sub_self]`. Set `d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (I ⧸ J)` to `{ toFun := fun x => Submodule.Quotient.mk ⟨_, hsub x⟩ map_zero' := by`. Rewrite using `[← Submodule.Quotient.mk_zero]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [map_zero, sub_zero, ZeroMemClass.coe_zero]`. Use the proof step `map_add' := fun x y => by`. Rewrite using `[← Submodule.Quotient.mk_add]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [map_add, Submodule.coe_add]`. Use `abel }`. Take `⟨u, hu, -⟩` from `hδuniv (I ⧸ J) d (fun o x => by show Submodule.Quotient.mk _ = o • Submodule.Quotient.mk _`.

Rewrite using `[← Submodule.Quotient.mk_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show _ = (D.fin.sO (D.ptIdx 0)).1 o * (x - _)`. Simplify using `only [map_mul, hπs, mul_sub])`.

Use the proof step `(fun x y => by show Submodule.Quotient.mk _ = (D.ptMap 0).1 x • Submodule.Quotient.mk _ + (D.ptMap 0).1 y • Submodule.Quotient.mk _`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.mem_comap]`. Establish `hm : (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) * (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b}` using `Submodule.subset_span ⟨_, hsub x, _, hsub y, rfl⟩`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use `show x * y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 (x * y)) - ((D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) * (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) + (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y) * (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) = _`.

Rewrite using `[map_mul, map_mul]`. Use the proof step `ring)`. Establish `hπF : (D.ptMap 0).1 (F (D.ptIdx 0)) = 0` using `(hmemA F).1 hh`. Establish `hx : F (D.ptIdx 0) ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b}`. Establish `h1` using `hu (F (D.ptIdx 0))`.

Rewrite `h1` using `[h0, map_zero]`. Establish `h3` using `Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)`. Simplify `h3` using `[hπF]`. Establish `hlift : ∀ z ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b}, f (Pi.single (D.ptIdx 0) z) ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C))`. Introduce `z hz`.

Unfold `_root_.ReciprocityTheory.PGsh.Up.sqIdeal`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, b, hb, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨f (Pi.single _ a), (hmemA _).2 (by rw [Pi.single_eq_same]; exact ha), f (Pi.single _ b), (hmemA _).2 (by rw [Pi.single_eq_same]; exact hb), by rw [Pi.single_mul, hfmul]⟩`.

Consider the case `zero => rw [Pi.single_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Pi.single_add, map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`.

Establish `hs : (Pi.single (D.ptIdx 0) (c • x) : ∀ i, (D.fin.AAx i).carrier) = c • (Pi.single (D.ptIdx 0) x : ∀ i, (D.fin.AAx i).carrier)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = D.ptIdx 0`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hj]`. Rewrite using `[hs, map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Set `G` to `F - Pi.single (D.ptIdx 0) (F (D.ptIdx 0))`. Set `E : ∀ i, (D.fin.AAx i).carrier` to `1 - Pi.single (D.ptIdx 0) 1`.

Establish `hG : E * G = G`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = D.ptIdx 0`. Substitute `hj` using the available equality. Simplify using `[E, G]`.

Simplify using `[E, G, Pi.single_eq_of_ne hj]`. Establish `hEmem : f E ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)` using `(hmemA E).2 (by simp [E])`. Establish `hGmem : f G ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)` using `(hmemA G).2 (by simp [G])`. Establish `hF : f F = f (Pi.single (D.ptIdx 0) (F (D.ptIdx 0))) + f G`. Rewrite using `[← map_add]`.

Use `congr 1`. Simplify using `[G]`. Use `show f F ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C))`. Rewrite using `[hF]`. Use `add_mem (hlift _ hx) ?_` and prove the remaining obligations.

Rewrite using `[← hG, hfmul]`. Unfold `_root_.ReciprocityTheory.PGsh.Up.sqIdeal`. Conclude with `Submodule.subset_span ⟨_, hEmem, _, hGmem, rfl⟩`. Introduce `hsq`. Establish `P : ∀ h ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), ∃ F', f F' = h ∧ δ (F' (D.ptIdx 0)) = 0`.

Introduce `h hh'`. Unfold `_root_.ReciprocityTheory.PGsh.Up.sqIdeal at hh'`. Proceed by induction on `hh' using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨h1, hh1, h2, hh2, rfl⟩` from `hz`.

Take `⟨F1, rfl⟩` from `hle hh1`. Take `⟨F2, rfl⟩` from `hle hh2`. Use `⟨F1 * F2, hfmul _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, hδder, (hmemA F1).1 hh1, (hmemA F2).1 hh2, zero_smul, zero_smul, add_zero]`. Consider the case `zero => exact ⟨0, map_zero f, by rw [Pi.zero_apply, map_zero]⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨F1, rfl, h1⟩` from `hx`. Take `⟨F2, rfl, h2⟩` from `hy`. Conclude with `⟨F1 + F2, map_add f _ _, by rw [Pi.add_apply, map_add, h1, h2, add_zero]⟩`. Consider the case `smul c x _ hx`.

Take `⟨F1, rfl, h1⟩` from `hx`. Use `⟨c • F1, map_smul f _ _, ?_⟩` and prove the remaining obligations. Use `show δ ((D.fin.sO (D.ptIdx 0)).1 c * F1 (D.ptIdx 0)) = 0`. Rewrite using `[hδlin, h1, smul_zero]`. Take `⟨F', hF', hδF'⟩` from `P _ hsq`.

Rewrite `hδF'` using `[finj hF']`. Conclude with `hδF'`. Introduce `a ⟨h1, hh1⟩ ⟨h2, hh2⟩ l hrel hl`. Take `⟨F1, rfl⟩ : h1 ∈ LinearMap.range f` from `hle hh1`. Take `⟨F2, rfl⟩ : h2 ∈ LinearMap.range f` from `hle hh2`.

Rewrite `hl`, the goal using `[hφ]`. Establish `hτ : ∀ k, p • D.L.τ k 0 = 0` using `fun k => by simpa using D.L.τ_tors k 0`. Establish `hmod : ∀ (x : B.G Tw.O) (n : ℕ), p • x = 0 → ((n : ZMod p).val) • x = n • x`. Introduce `x n hx`. Rewrite using `[ZMod.val_natCast]`.

Use `conv_rhs => rw [← Nat.mod_add_div n p]`. Rewrite using `[add_nsmul, mul_comm, ← smul_smul, hx, smul_zero, add_zero]`. Establish `hact : ∀ (s : _root_.ReciprocityTheory.PGsh.Up.TT p g) hp, (↑(D.A.act a Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩) : B.G Tw.O) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ ( …`. Introduce `s hp`. Establish `hsplit : (⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩ : ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) = ∑ j, (PadicInt.toZMod (s j)).val • ⟨D.L.τ j 0, (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (hτ j)⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red]`. Rewrite using `[hsplit, map_sum]`. Simplify using `only [map_nsmul]`. Use `push_cast`.

Simplify using `only [D.L.ρ_spec]`. Simplify using `only [_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hc : (∑ j, PadicInt.toZMod (D.H.ρ a k j) * PadicInt.toZMod (s j)) = ((∑ j, (PadicInt.toZMod (D.H.ρ a k j)).val * (PadicInt.toZMod (s j)).val : ℕ) : ZMod p)`.

Simplify using `only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]`. Rewrite using `[hc, hmod _ _ (hτ k), Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `tr : ∀ (G : ∀ i, (D.fin.AAx i).carrier) (j j' : D.fin.ι) (χ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O) (χ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j') Tw.O), j = j' → HEq χ χ' → χ.1 (G j) = χ'.1 (G j')`.

Introduce and unpack `G j j' χ χ' rfl h`. Rewrite using `[eq_of_heq h]`. Establish `hpt : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), ψ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id _ → ∀ t, B.map ψ (D.fin.y j) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t → D.ptIdx t = j ∧ HEq (D.ptMap t) ψ`. Introduce `j ψ hψ t ht`. Take `⟨i1, φ1, -, -, huniq⟩` from `D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ (D.pt_p t)`.

Take `⟨e1, e2⟩` from `huniq j ψ hψ ht`. Take `⟨e3, e4⟩` from `huniq _ _ (hspec t).1 (hspec t).2`. Conclude with `⟨e3.trans e1.symm, e4.trans e2.symm⟩`. Establish `hyt` using `(_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).1 ((D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0))) ⟨D.fin.y (D.ptIdx 0), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩).2`. Take `⟨i, φa, hφs, hφz, -⟩` from `D.fin.univ _ (D.fin.sO (D.ptIdx 0)) _ hyt`.

Establish `hcomp : ∀ (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) Tw.O), ψ.comp (D.fin.sO (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.LHom.id _ → ∀ s, B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g …`. Introduce `ψ hψ s hs`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ψ.comp (φa.comp (D.fin.sO i)) = _`. Rewrite using `[hφs, hψ]`.

Rewrite using `[B.map_comp, hφz, D.A.act_nat a (D.fin.sO _) (_root_.ReciprocityTheory.PGsh.LHom.id _) ψ hψ]`. Establish `e1 : (⟨B.map ψ (D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (by rw [hs]; exact D.pt_p _)⟩ : ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) = ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), (_root_.R …` using `Subtype.ext hs`. Rewrite using `[e1]`. Conclude with `hact s _`. Establish `hVW0 : _root_.ReciprocityTheory.PGsh.Up.red p g 0 = 0` using `by funext k; simp [_root_.ReciprocityTheory.PGsh.Up.red]`.

Establish `h00` using `hcomp (D.ptMap 0) (hspec 0).1 0 (by rw [hVW0]; exact (hspec 0).2)`. Rewrite `h00` using `[Matrix.mulVec_zero, hVW0]`. Take `⟨hi, -⟩` from `hpt i _ h00.1 0 h00.2`. Substitute `hi` using the available equality. Establish `hmain : φa.1 (F1 (D.ptIdx 0)) = F2 (D.ptIdx 0)`.

Rewrite using `[← sub_eq_zero]`. Apply `D.fin.sep` to reduce the goal to its premises. Introduce `ψ hψ`. Establish `hz : p • B.map ψ (D.fin.y (D.ptIdx 0)) = 0` using `by rw [← map_nsmul, D.fin.y_p, map_zero]`. Take `⟨t, ht⟩` from `D.L.τ_basis.2 ⟨_, hz⟩`.

Set `s : _root_.ReciprocityTheory.PGsh.Up.TT p g` to `fun k => ((t k).val : ℤ_[p])`. Establish `hts : _root_.ReciprocityTheory.PGsh.Up.red p g s = t` using `by funext k; simp [s, _root_.ReciprocityTheory.PGsh.Up.red]`. Establish `hs : B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s)`. Rewrite using `[hts]`. Conclude with `(congrArg Subtype.val ht).symm`.

Take `⟨c1, c2⟩` from `hcomp ψ hψ s hs`. Take `⟨j1, k1⟩` from `hpt _ _ c1 _ c2`. Take `⟨j2, k2⟩` from `hpt _ _ hψ _ hs`. Establish `hr : f F2 (_root_.ReciprocityTheory.PGsh.Up.red p g s) = f F1 (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s))` using `hrel s`. Rewrite `hr` using `[hf, hf]`.

Establish `hr'` using `hinj hr`. Rewrite `hr'` using `[tr F2 _ _ _ _ j2 k2, tr F1 _ _ _ _ j1 k1]`. Use `show ψ.1 (φa.1 (F1 (D.ptIdx 0)) - F2 (D.ptIdx 0)) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `hr'.symm`.

Rewrite using `[← hmain]`. Conclude with `hδeq a φa hφs hφz _ l hl`.
-/
theorem _root_.GlobalTheory.evCot_of_univDer :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), ∃ δ : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g,
    (∀ o f, δ ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • δ f) ∧ (∀ f f', δ (f * f') = (D.ptMap 0).1 f • δ f' + (D.ptMap 0).1 f' • δ f) ∧
    (∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (d : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ M),
      (∀ o f, d ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • d f) → (∀ f f', d (f * f') = (D.ptMap 0).1 f • d f' + (D.ptMap 0).1 f' • d f) →
      ∃! u : _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M, ∀ f, d f = u (δ f)) ∧
    ∀ (a : Oe) (α : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) (D.fin.AAx (D.ptIdx 0))), α.comp (D.fin.sO (D.ptIdx 0)) = (D.fin.sO (D.ptIdx 0)) →
      B.map α (D.fin.y (D.ptIdx 0)) = (D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)) ⟨(D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩ : B.G (D.fin.AAx (D.ptIdx 0))) →
      ∀ f (l : Fin g → (Tw.O : Type)), δ f = Submodule.Quotient.mk l → δ (α.1 f) = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvCotStatement D) := by
  intro hU R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvCotStatement
  intro C _ _ hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  have hsec : ∀ t c, (D.ptMap t).1 ((D.fin.sO (D.ptIdx t)).1 c) = c := fun t c =>
    congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 c) (hspec t).1
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => hsec t o }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have hfmul : ∀ F G, f (F * G) = f F * f G := fun F G => by
    funext x; simp only [hf, Pi.mul_apply, map_mul]
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  have finj : Function.Injective f := fun F G h =>
    hinjΨ (funext fun x => hinj (congrFun h x))
  obtain ⟨δ, hδlin, hδder, hδuniv, hδeq⟩ := hU D
  clear hU
  have hπs : ∀ c, (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c) = c := hsec 0
  have hδ1 : δ 1 = 0 := by
    have h := hδder 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h2 : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hδs : ∀ c, δ ((D.fin.sO (D.ptIdx 0)).1 c) = 0 := fun c => by
    have h := hδlin c 1
    rw [mul_one, hδ1, smul_zero] at h
    exact h

  have hδsurj : Function.Surjective δ := by
    let N : Submodule Tw.O.carrier (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g) :=
      { carrier := Set.range δ
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add δ x y⟩
        zero_mem' := ⟨0, map_zero δ⟩
        smul_mem' := by rintro c _ ⟨x, rfl⟩; exact ⟨_, hδlin c x⟩ }
    let d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g ⧸ N) :=
      N.mkQ.toAddMonoidHom.comp δ
    obtain ⟨u, -, huniq⟩ := hδuniv _ d
      (fun o x => by simp only [d, AddMonoidHom.comp_apply, hδlin]; exact map_smul N.mkQ o (δ x))
      (fun x y => by
        simp only [d, AddMonoidHom.comp_apply, hδder]
        exact (map_add N.mkQ _ _).trans (by rw [map_smul, map_smul]; rfl))
    have h1 := huniq N.mkQ (fun x => rfl)
    have h2 := huniq 0 (fun x => by
      show N.mkQ (δ x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨x, rfl⟩)
    intro q
    have hq : N.mkQ q = 0 := by rw [h1.trans h2.symm]; rfl
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    exact hq
  have hmemA : ∀ F, f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ↔ (D.ptMap 0).1 (F (D.ptIdx 0)) = 0 := fun F => by
    unfold _root_.ReciprocityTheory.PGsh.L2.augIdeal
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply, hf]
    refine ⟨fun h => hinj (h.2.trans (map_zero _).symm), fun h => ⟨?_, by rw [h, map_zero]⟩⟩
    rw [himg]; exact ⟨F, rfl⟩
  have hle : _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ≤ LinearMap.range f := fun h hh => by
    unfold _root_.ReciprocityTheory.PGsh.L2.augIdeal at hh; rw [← himg]; exact (Submodule.mem_inf.1 hh).1
  let e := LinearEquiv.ofInjective f finj
  let Δ : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] _root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g :=
    { toFun := fun F => δ (F (D.ptIdx 0))
      map_add' := fun F G => map_add δ _ _
      map_smul' := fun c F => hδlin c _ }
  let φ := Δ ∘ₗ (e.symm : LinearMap.range f →ₗ[Tw.O.carrier] _) ∘ₗ Submodule.inclusion hle
  have hφ : ∀ F (hF : f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), φ ⟨f F, hF⟩ = δ (F (D.ptIdx 0)) := fun F hF => by
    have he : e.symm ⟨f F, hle hF⟩ = F := e.symm_apply_eq.2 (Subtype.ext (by simp [e]))
    show Δ (e.symm ⟨f F, hle hF⟩) = _
    rw [he]; rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := hδsurj q
    have hx' : (D.ptMap 0).1 (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) = 0 := by
      rw [map_sub, hπs, sub_self]
    have hmem : f (Pi.single (D.ptIdx 0) (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) ∈
        _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA _).2 (by rw [Pi.single_eq_same]; exact hx')
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hφ, Pi.single_eq_same, map_sub, hδs, sub_zero]
  · ext ⟨h, hh⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    obtain ⟨F, rfl⟩ : h ∈ LinearMap.range f := hle hh
    rw [hφ F hh]
    constructor
    · intro h0
      let π0 : (D.fin.AAx (D.ptIdx 0)).carrier →ₗ[Tw.O.carrier] Tw.O.carrier :=
        { toFun := (D.ptMap 0).1
          map_add' := map_add _
          map_smul' := fun c x => by
            show (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c * x) = c * (D.ptMap 0).1 x
            rw [map_mul, hπs] }
      let I := LinearMap.ker π0
      let J : Submodule Tw.O.carrier I := Submodule.comap I.subtype
        (Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b})
      have hsub : ∀ x, x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) ∈ I := fun x => by
        rw [LinearMap.mem_ker]
        show (D.ptMap 0).1 (x - _) = 0
        rw [map_sub, hπs, sub_self]
      let d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (I ⧸ J) :=
        { toFun := fun x => Submodule.Quotient.mk ⟨_, hsub x⟩
          map_zero' := by
            rw [← Submodule.Quotient.mk_zero]; congr 1; apply Subtype.ext
            simp only [map_zero, sub_zero, ZeroMemClass.coe_zero]
          map_add' := fun x y => by
            rw [← Submodule.Quotient.mk_add]; congr 1; apply Subtype.ext
            simp only [map_add, Submodule.coe_add]; abel }
      obtain ⟨u, hu, -⟩ := hδuniv (I ⧸ J) d
        (fun o x => by
          show Submodule.Quotient.mk _ = o • Submodule.Quotient.mk _
          rw [← Submodule.Quotient.mk_smul]; congr 1; apply Subtype.ext
          show _ = (D.fin.sO (D.ptIdx 0)).1 o * (x - _)
          simp only [map_mul, hπs, mul_sub])
        (fun x y => by
          show Submodule.Quotient.mk _ = (D.ptMap 0).1 x • Submodule.Quotient.mk _ +
            (D.ptMap 0).1 y • Submodule.Quotient.mk _
          rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
            ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.mem_comap]
          have hm : (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) *
              (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) ∈
              Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b} :=
            Submodule.subset_span ⟨_, hsub x, _, hsub y, rfl⟩
          convert hm using 1
          show x * y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 (x * y)) -
            ((D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) * (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) +
            (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y) * (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) = _
          rw [map_mul, map_mul]
          ring)
      have hπF : (D.ptMap 0).1 (F (D.ptIdx 0)) = 0 := (hmemA F).1 hh
      have hx : F (D.ptIdx 0) ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b} := by
        have h1 := hu (F (D.ptIdx 0))
        rw [h0, map_zero] at h1
        have h3 := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
        simpa [hπF] using h3
      have hlift : ∀ z ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b},
          f (Pi.single (D.ptIdx 0) z) ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)) := by
        intro z hz
        unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          exact Submodule.subset_span ⟨f (Pi.single _ a), (hmemA _).2 (by rw [Pi.single_eq_same]; exact ha),
            f (Pi.single _ b), (hmemA _).2 (by rw [Pi.single_eq_same]; exact hb),
            by rw [Pi.single_mul, hfmul]⟩
        | zero => rw [Pi.single_zero, map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [Pi.single_add, map_add]; exact add_mem hx hy
        | smul c x _ hx =>
          have hs : (Pi.single (D.ptIdx 0) (c • x) : ∀ i, (D.fin.AAx i).carrier) =
              c • (Pi.single (D.ptIdx 0) x : ∀ i, (D.fin.AAx i).carrier) := by
            funext j
            by_cases hj : j = D.ptIdx 0
            · subst hj; simp
            · simp [Pi.single_eq_of_ne hj]
          rw [hs, map_smul]; exact Submodule.smul_mem _ c hx
      let G := F - Pi.single (D.ptIdx 0) (F (D.ptIdx 0))
      let E : ∀ i, (D.fin.AAx i).carrier := 1 - Pi.single (D.ptIdx 0) 1
      have hG : E * G = G := by
        funext j
        by_cases hj : j = D.ptIdx 0
        · subst hj; simp [E, G]
        · simp [E, G, Pi.single_eq_of_ne hj]
      have hEmem : f E ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA E).2 (by simp [E])
      have hGmem : f G ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA G).2 (by simp [G])
      have hF : f F = f (Pi.single (D.ptIdx 0) (F (D.ptIdx 0))) + f G := by
        rw [← map_add]; congr 1; simp [G]
      show f F ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C))
      rw [hF]
      refine add_mem (hlift _ hx) ?_
      rw [← hG, hfmul]
      unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal
      exact Submodule.subset_span ⟨_, hEmem, _, hGmem, rfl⟩
    · intro hsq
      have P : ∀ h ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), ∃ F', f F' = h ∧ δ (F' (D.ptIdx 0)) = 0 := by
        intro h hh'
        unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal at hh'
        induction hh' using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨h1, hh1, h2, hh2, rfl⟩ := hz
          obtain ⟨F1, rfl⟩ := hle hh1
          obtain ⟨F2, rfl⟩ := hle hh2
          refine ⟨F1 * F2, hfmul _ _, ?_⟩
          rw [Pi.mul_apply, hδder, (hmemA F1).1 hh1, (hmemA F2).1 hh2, zero_smul, zero_smul, add_zero]
        | zero => exact ⟨0, map_zero f, by rw [Pi.zero_apply, map_zero]⟩
        | add x y _ _ hx hy =>
          obtain ⟨F1, rfl, h1⟩ := hx
          obtain ⟨F2, rfl, h2⟩ := hy
          exact ⟨F1 + F2, map_add f _ _, by rw [Pi.add_apply, map_add, h1, h2, add_zero]⟩
        | smul c x _ hx =>
          obtain ⟨F1, rfl, h1⟩ := hx
          refine ⟨c • F1, map_smul f _ _, ?_⟩
          show δ ((D.fin.sO (D.ptIdx 0)).1 c * F1 (D.ptIdx 0)) = 0
          rw [hδlin, h1, smul_zero]
      obtain ⟨F', hF', hδF'⟩ := P _ hsq
      rw [finj hF'] at hδF'
      exact hδF'
  · intro a ⟨h1, hh1⟩ ⟨h2, hh2⟩ l hrel hl
    obtain ⟨F1, rfl⟩ : h1 ∈ LinearMap.range f := hle hh1
    obtain ⟨F2, rfl⟩ : h2 ∈ LinearMap.range f := hle hh2
    rw [hφ] at hl ⊢
    have hτ : ∀ k, p • D.L.τ k 0 = 0 := fun k => by simpa using D.L.τ_tors k 0
    have hmod : ∀ (x : B.G Tw.O) (n : ℕ), p • x = 0 → ((n : ZMod p).val) • x = n • x := by
      intro x n hx
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.mod_add_div n p]
      rw [add_nsmul, mul_comm, ← smul_smul, hx, smul_zero, add_zero]
    have hact : ∀ (s : _root_.ReciprocityTheory.PGsh.Up.TT p g) hp,
        (↑(D.A.act a Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩) : B.G Tw.O) =
          _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := by
      intro s hp
      have hsplit : (⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩ : ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) =
          ∑ j, (PadicInt.toZMod (s j)).val • ⟨D.L.τ j 0, (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (hτ j)⟩ := by
        apply Subtype.ext
        simp [_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red]
      rw [hsplit, map_sum]
      simp only [map_nsmul]
      push_cast
      simp only [D.L.ρ_spec]
      simp only [_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc : (∑ j, PadicInt.toZMod (D.H.ρ a k j) * PadicInt.toZMod (s j)) =
          ((∑ j, (PadicInt.toZMod (D.H.ρ a k j)).val * (PadicInt.toZMod (s j)).val : ℕ) : ZMod p) := by
        simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
      rw [hc, hmod _ _ (hτ k), Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    have tr : ∀ (G : ∀ i, (D.fin.AAx i).carrier) (j j' : D.fin.ι) (χ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O)
        (χ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j') Tw.O), j = j' → HEq χ χ' → χ.1 (G j) = χ'.1 (G j') := by
      rintro G j j' χ χ' rfl h
      rw [eq_of_heq h]
    have hpt : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), ψ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id _ →
        ∀ t, B.map ψ (D.fin.y j) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t → D.ptIdx t = j ∧ HEq (D.ptMap t) ψ := by
      intro j ψ hψ t ht
      obtain ⟨i1, φ1, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ (D.pt_p t)
      obtain ⟨e1, e2⟩ := huniq j ψ hψ ht
      obtain ⟨e3, e4⟩ := huniq _ _ (hspec t).1 (hspec t).2
      exact ⟨e3.trans e1.symm, e4.trans e2.symm⟩
    have hyt := (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).1 ((D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)))
        ⟨D.fin.y (D.ptIdx 0), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩).2
    obtain ⟨i, φa, hφs, hφz, -⟩ := D.fin.univ _ (D.fin.sO (D.ptIdx 0)) _ hyt
    have hcomp : ∀ (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) Tw.O), ψ.comp (D.fin.sO (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.LHom.id _ →
        ∀ s, B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s) →
        (ψ.comp φa).comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
          B.map (ψ.comp φa) (D.fin.y i) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := by
      intro ψ hψ s hs
      refine ⟨?_, ?_⟩
      · show ψ.comp (φa.comp (D.fin.sO i)) = _
        rw [hφs, hψ]
      · rw [B.map_comp, hφz, D.A.act_nat a (D.fin.sO _) (_root_.ReciprocityTheory.PGsh.LHom.id _) ψ hψ]
        have e1 : (⟨B.map ψ (D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (by rw [hs]; exact D.pt_p _)⟩ :
            ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) = ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.pt_p _)⟩ :=
          Subtype.ext hs
        rw [e1]
        exact hact s _
    have hVW0 : _root_.ReciprocityTheory.PGsh.Up.red p g 0 = 0 := by funext k; simp [_root_.ReciprocityTheory.PGsh.Up.red]
    have h00 := hcomp (D.ptMap 0) (hspec 0).1 0 (by rw [hVW0]; exact (hspec 0).2)
    rw [Matrix.mulVec_zero, hVW0] at h00
    obtain ⟨hi, -⟩ := hpt i _ h00.1 0 h00.2
    subst hi
    have hmain : φa.1 (F1 (D.ptIdx 0)) = F2 (D.ptIdx 0) := by
      rw [← sub_eq_zero]
      apply D.fin.sep
      intro ψ hψ
      have hz : p • B.map ψ (D.fin.y (D.ptIdx 0)) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
      obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
      let s : _root_.ReciprocityTheory.PGsh.Up.TT p g := fun k => ((t k).val : ℤ_[p])
      have hts : _root_.ReciprocityTheory.PGsh.Up.red p g s = t := by funext k; simp [s, _root_.ReciprocityTheory.PGsh.Up.red]
      have hs : B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s) := by
        rw [hts]; exact (congrArg Subtype.val ht).symm
      obtain ⟨c1, c2⟩ := hcomp ψ hψ s hs
      obtain ⟨j1, k1⟩ := hpt _ _ c1 _ c2
      obtain ⟨j2, k2⟩ := hpt _ _ hψ _ hs
      have hr : f F2 (_root_.ReciprocityTheory.PGsh.Up.red p g s) = f F1 (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := hrel s
      rw [hf, hf] at hr
      have hr' := hinj hr
      rw [tr F2 _ _ _ _ j2 k2, tr F1 _ _ _ _ j1 k1] at hr'
      show ψ.1 (φa.1 (F1 (D.ptIdx 0)) - F2 (D.ptIdx 0)) = 0
      rw [map_sub, sub_eq_zero]
      exact hr'.symm
    rw [← hmain]
    exact hδeq a φa hφs hφz _ l hl

end GlobalTheory
