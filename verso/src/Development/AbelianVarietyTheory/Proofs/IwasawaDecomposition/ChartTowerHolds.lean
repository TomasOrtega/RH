import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartEmbeddingHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht GlobalTheory.Ex GlobalTheory.FullPoint MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.Tower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `left_eq_mul.1 h`. Consider the case `succ n ih => rw [succ_nsmul, hf, ih, pow_succ]`.
-/
theorem nsmul_pow {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ)
    (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

/- English proof (translation)
Take `⟨j, rfl⟩` from `h`. Establish `hn : 0 < n` using `Nat.pos_of_mul_pos_right hm`. Rewrite using `[Nat.mul_div_cancel_left _ hn, nsmul_pow _ (I.add _), I.tower n j hn (Nat.pos_of_mul_pos_left hm)]`.
-/
theorem ev_eq_of_dvd {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) {n m : ℕ} (h : n ∣ m) (hm : 0 < m) (a : D.La) : I.ev n a = I.ev m ((m / n) • a) := by
  obtain ⟨j, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  rw [Nat.mul_div_cancel_left _ hn, nsmul_pow _ (I.add _), I.tower n j hn (Nat.pos_of_mul_pos_left hm)]

/- English proof (translation)
Take `⟨φ, g₁, g₂, g₃, g₄, g₅⟩` from `h`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Establish `hM' : 0 < l'.M` using `lt_of_lt_of_le (by norm_num) l'.three_le`. Take `⟨w, hw, -⟩` from `ν.lin`. Use `⟨φ ≫ ν.φ, g₁.comp ν.cart, LBIso.trans o.P.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB ob.t.PP.isLB _) g₂ (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame ob.t.PP.L (fun _ : PUnit => φ ≫ ν.φ) (fun _ => ν.φ) (fun _ => 1) φ fun _ => rfl) ⟨w, hw⟩), fun x => ?_, fun v …` and prove the remaining obligations.

Rewrite using `[← Category.assoc, g₃, Category.assoc, ν.act, Category.assoc]`. Rewrite using `[ev_eq_of_dvd o.I hl.2.2 l'.A_pos]`. Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ) (g₄ _))).trans ?_` and prove the remaining obligations. Rewrite using `[nsmul_pow _ ob'.etaA_add]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₂ v)).trans (Category.assoc _ _ _).symm)`.

Take `⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l'.Mb, ∃ e ∈ l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1` from `Submodule.mem_sup.1 (by rw [l'.coprime]; trivial)`. Take `⟨c, hc⟩` from `exists_eq_nsmul l l.prod (hl.2.1 hf) hv`. Establish `e1 : v = e • v + l.M • c` using `by rw [← hc, ← add_smul, add_comm, hfe, one_smul]`. Establish `e2 : o.I.ev l.M v = o.I.ev l.M (e • v)` using `by conv_lhs => rw [e1]`. Rewrite using `[o.I.add, (o.I.ker _ hM _).2 ⟨c, rfl⟩, _root_.mul_one]`.

Rewrite using `[e2, ev_eq_of_dvd o.I hl.1 hM', ← eta_smul ob (e := e) (by rw [← hfe, add_sub_cancel_right]; exact hl.2.1 hf) v]`. Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ) (g₅ _ (nsmul_mem (Submodule.smul_mem_smul he Submodule.mem_top) _)))).trans ?_` and prove the remaining obligations. Rewrite using `[nsmul_pow _ ob'.eta_add]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₁ _)).trans (Category.assoc _ _ _).symm)`.
-/
theorem isFibre_lower {l l' : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l' B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {ob : Obj D l b s} {ob' : Obj D l' b' s'} (hl : l.Dvd l')
    {r : S' ⟶ S} (ν : SABMap ob'.t ob.t r)
    (h₁ : ∀ a, (ob'.eta a ^ (l'.M / l.M)).left ≫ ν.φ = r ≫ (ob.eta a).left)
    (h₂ : ∀ a, (ob'.etaA a ^ (l'.A / l.A)).left ≫ ν.φ = r ≫ (ob.etaA a).left)
    {K : Type} [Field K] {y : Sp K ⟶ S'} {o : Full D K} (h : IsFibre ob' y o) : IsFibre ob (y ≫ r) o := by
  obtain ⟨φ, g₁, g₂, g₃, g₄, g₅⟩ := h
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : 0 < l'.M := lt_of_lt_of_le (by norm_num) l'.three_le
  obtain ⟨w, hw, -⟩ := ν.lin
  refine ⟨φ ≫ ν.φ, g₁.comp ν.cart, LBIso.trans o.P.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB ob.t.PP.isLB _) g₂
    (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (chartPullSame ob.t.PP.L (fun _ : PUnit => φ ≫ ν.φ) (fun _ => ν.φ) (fun _ => 1) φ fun _ => rfl) ⟨w, hw⟩),
    fun x => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [← Category.assoc, g₃, Category.assoc, ν.act, Category.assoc]
  · rw [ev_eq_of_dvd o.I hl.2.2 l'.A_pos]
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ) (g₄ _))).trans ?_
    rw [nsmul_pow _ ob'.etaA_add]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₂ v)).trans (Category.assoc _ _ _).symm)
  · obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l'.Mb, ∃ e ∈ l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
      Submodule.mem_sup.1 (by rw [l'.coprime]; trivial)
    obtain ⟨c, hc⟩ := exists_eq_nsmul l l.prod (hl.2.1 hf) hv
    have e1 : v = e • v + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
    have e2 : o.I.ev l.M v = o.I.ev l.M (e • v) := by
      conv_lhs => rw [e1]
      rw [o.I.add, (o.I.ker _ hM _).2 ⟨c, rfl⟩, _root_.mul_one]
    rw [e2, ev_eq_of_dvd o.I hl.1 hM',
      ← eta_smul ob (e := e) (by rw [← hfe, add_sub_cancel_right]; exact hl.2.1 hf) v]
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ)
      (g₅ _ (nsmul_mem (Submodule.smul_mem_smul he Submodule.mem_top) _)))).trans ?_
    rw [nsmul_pow _ ob'.eta_add]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₁ _)).trans (Category.assoc _ _ _).symm)

/- English proof (translation)
Use `IsFractionRing.of_field _ _ fun z => ?_` and prove the remaining obligations. Break down `le_total ‖z‖ 1 with h | h` into its components or cases. Conclude with `⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩`. Conclude with `⟨1, ⟨z⁻¹, by change ‖z⁻¹‖ ≤ 1; rw [norm_inv]; exact inv_le_one_of_one_le₀ h⟩, by rw [map_one, one_div]; exact (inv_inv z).symm⟩`.
-/
theorem isFractionRing_ball (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  rcases le_total ‖z‖ 1 with h | h
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, by change ‖z⁻¹‖ ≤ 1; rw [norm_inv]; exact inv_le_one_of_one_le₀ h⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

section Model

variable {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`.
-/
theorem j_s (Y : Model Xo c β) : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

/- English proof (translation)
Use `projProper _ _ _ Y.proj` as an intermediate fact. Use `isFractionRing_ball ↥C.S` as an intermediate fact. Set `alg : O →+* intO ↥C.S` to `(f.comp β).codRestrict _ hf`. Establish `hE : ValuativeCriterion.Existence Y.s` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1`. Take `⟨⟨t⟩⟩` from `hE { R := ↥(intO ↥C.S), K := ↥C.S, i₁ := y ≫ Y.j, i₂ := spMap alg, commSq := ⟨by`.

Rewrite using `[Category.assoc, j_s, ← Category.assoc, hy, ← spMap_comp]`. Conclude with `spMap_comp alg (intO ↥C.S).subtype⟩ }`. Conclude with `⟨⟨alg, f, rfl, y, hy, t.l, t.fac_right, t.fac_left⟩, rfl, rfl⟩`.
-/
theorem exists_ptC (Y : Model Xo c β) {p : ℕ} (C : SCF p) (f : c.F →+* ↥C.S) (hf : ∀ x, ‖f (β x)‖ ≤ 1)
    (y : Sp ↥C.S ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap f) : ∃ P : PointsOfFlagModel.PtC Y C, P.fK = f ∧ P.y = y := by
  have := projProper _ _ _ Y.proj
  have := isFractionRing_ball ↥C.S
  let alg : O →+* intO ↥C.S := (f.comp β).codRestrict _ hf
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨t⟩⟩ := hE { R := ↥(intO ↥C.S), K := ↥C.S, i₁ := y ≫ Y.j, i₂ := spMap alg, commSq := ⟨by
    rw [Category.assoc, j_s, ← Category.assoc, hy, ← spMap_comp]
    exact spMap_comp alg (intO ↥C.S).subtype⟩ }
  exact ⟨⟨alg, f, rfl, y, hy, t.l, t.fac_right, t.fac_left⟩, rfl, rfl⟩

end Model

variable {Xo : ∀ l : Geo.Tor.Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

/- English proof (translation)
Establish `h₃ : P.yt = P'.yt` using `base_ext i _ _ (by rw [P.ext, P'.ext, h₂])`. Establish `h₄ : P.alg = P'.alg` using `RingHom.ext fun x => Subtype.ext ((DFunLike.congr_fun P.compat x).trans (by rw [h₁]; exact (DFunLike.congr_fun P'.compat x).symm))`. Consider the cases of `P`. Consider the cases of `P'`. Simplify using `only at h₁ h₂ h₃ h₄`.

Substitute `h₁ h₂ h₃ h₄` using the available equality. Both sides reduce to the same expression.
-/
theorem ptC_ext {i : Idx H p} {C : SCF p} {P P' : PointsOfFlagModel.PtC (Y i) C} (h₁ : P.fK = P'.fK) (h₂ : P.y = P'.y) : P = P' := by
  have h₃ : P.yt = P'.yt := base_ext i _ _ (by rw [P.ext, P'.ext, h₂])
  have h₄ : P.alg = P'.alg := RingHom.ext fun x => Subtype.ext
    ((DFunLike.congr_fun P.compat x).trans (by rw [h₁]; exact (DFunLike.congr_fun P'.compat x).symm))
  cases P; cases P'
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂ h₃ h₄
  rfl

/- English proof (translation)
Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Conclude with `(Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)`. Establish `a₁ : σ'.left ≫ t'.G.hom = 𝟙 _` using `Over.w σ'`. Establish `a₂ : σ.left ≫ t.G.hom = 𝟙 _` using `Over.w σ`. Use `(Category.assoc _ _ _).trans ((congrArg (σ'.left ≫ ·) ν.cart.1.w).trans ?_)` and prove the remaining obligations.

Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) a₁)).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) a₂)).symm` and prove the remaining obligations. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.
-/
theorem sec_cancel {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {T : SAB H X} {r : S' ⟶ S} {j : S ⟶ X}
    (ν : SABMap t' t r) (m : SABMap t T j) (σ' : MonoidalCategory.tensorUnit _ ⟶ t'.G)
    (σ : MonoidalCategory.tensorUnit _ ⟶ t.G) (e : σ'.left ≫ ν.φ ≫ m.φ = r ≫ σ.left ≫ m.φ) :
    σ'.left ≫ ν.φ = r ≫ σ.left := by
  apply m.cart.1.hom_ext
  · exact (Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)
  · have a₁ : σ'.left ≫ t'.G.hom = 𝟙 _ := Over.w σ'
    have a₂ : σ.left ≫ t.G.hom = 𝟙 _ := Over.w σ
    refine (Category.assoc _ _ _).trans ((congrArg (σ'.left ≫ ·) ν.cart.1.w).trans ?_)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) a₁)).trans ?_
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) a₂)).symm
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/- English proof (translation)
Establish `h` using `ObjMaps.exists_sab_comp mu m'`. Rewrite `h` using `[e]`. Take `⟨n, hn⟩` from `h`. Take `⟨ν, hν⟩` from `ObjMaps.exists_sab_cancel m n`. Conclude with `⟨ν, hn.symm.trans hν⟩`.
-/
theorem exists_sab_square {S S' X X' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {T : SAB H X} {T' : SAB H X'}
    {r : S' ⟶ S} {j : S ⟶ X} {j' : S' ⟶ X'} {τ : X' ⟶ X} (e : j' ≫ τ = r ≫ j) (m : SABMap t T j)
    (m' : SABMap t' T' j') (mu : SABMap T' T τ) : ∃ ν : SABMap t' t r, m'.φ ≫ mu.φ = ν.φ ≫ m.φ := by
  have h := ObjMaps.exists_sab_comp mu m'
  rw [e] at h
  obtain ⟨n, hn⟩ := h
  obtain ⟨ν, hν⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨ν, hn.symm.trans hν⟩

/- English proof (translation)
Use extensionality with `x`. Break down `V.mem_or_inv_mem x with hx | hx` into its components or cases. Conclude with `h ⟨x, hx⟩`. Simplify using `using h ⟨_, hx⟩`.
-/
theorem ringHom_ext_val {F K : Type} [Field F] [Field K] (V : ValuationSubring F) {f g : F →+* K}
    (h : ∀ x : V, f x = g x) : f = g := by
  ext x
  rcases V.mem_or_inv_mem x with hx | hx
  · exact h ⟨x, hx⟩
  · simpa using h ⟨_, hx⟩

/- English proof (translation)
Simplify using `only [Category.assoc]`. Rewrite using `[← h, ← reassoc_of% e₃, ← e₁, Category.assoc, pullback.condition, reassoc_of% e₂, reassoc_of% h']`.
-/
theorem base_square {S S' X X' F F' O O' T : Scheme.{0}} {j : S ⟶ X} {j' : S' ⟶ X'} {s : X ⟶ O} {s' : X' ⟶ O'}
    {q : S ⟶ F} {q' : S' ⟶ F'} {β : F ⟶ O} {β' : F' ⟶ O'} {b : O' ⟶ O} {τ : X' ⟶ X} {r : S' ⟶ S}
    {π' : X' ⟶ pullback s b} (h : j ≫ s = q ≫ β) (h' : j' ≫ s' = q' ≫ β') (e₁ : π' ≫ pullback.fst _ _ = τ)
    (e₂ : π' ≫ pullback.snd _ _ = s') (e₃ : j' ≫ τ = r ≫ j) (y : T ⟶ S') :
    ((y ≫ r) ≫ q) ≫ β = ((y ≫ q') ≫ β') ≫ b := by
  simp only [Category.assoc]
  rw [← h, ← reassoc_of% e₃, ← e₁, Category.assoc, pullback.condition, reassoc_of% e₂, reassoc_of% h']

/- English proof (translation)
Take `⟨b, π', r, hb, e₁, e₂, -, e₃, h₁, h₂⟩` from `h`. Take `⟨ν, hν⟩` from `exists_sab_square e₃ (Y i).m (Y i').m mu`. Use `⟨y' ≫ r, ⟨?_, isFibre_lower hl ν (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₁ a))) (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₂ a))) ho⟩, (congrArg (y' ≫ ·) e₃).trans (Category.assoc _ _ _).symm⟩` and prove the remaining obligations. Take `⟨g, hg⟩ : ∃ g : i.c.F →+* K, (y' ≫ r) ≫ pullback.snd _ _ = spMap g` from `⟨(Spec.preimage ((y' ≫ r) ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩`. Establish `e₄ : spMap (g.comp (i.c.V W).subtype) = spMap ((f'.comp (i'.c.V W).subtype).comp b)`.

Rewrite using `[spMap_comp, spMap_comp, spMap_comp, ← hg, ← hy]`. Conclude with `base_square (j_s (Y i)) (j_s (Y i')) e₁ e₂ e₃ y'`. Conclude with `hg.trans (congrArg spMap (ringHom_ext_val (i.c.V W) fun x => (DFunLike.congr_fun (spMap_inj e₄) x).trans (hf _ _ (hb x))))`.
-/
theorem exists_lower {i i' : Idx H p} {τ : (Y i').X ⟶ (Y i).X} {mu : SABMap (Y i').t (Y i).t τ} (hl : i.l.Dvd i'.l)
    (h : IsTrans i i' τ mu) {K : Type} [Field K] (f : i.c.F →+* K) (f' : i'.c.F →+* K)
    (hf : ∀ (x : i.c.F) (x' : i'.c.F), (x' : ℂ) = x → f' x' = f x) {y' : Sp K ⟶ (Xo i'.l).XF i'.c}
    (hy : y' ≫ pullback.snd _ _ = spMap f') {o : Full D K} (ho : IsFibre (Y i').oF y' o) :
    ∃ y : Sp K ⟶ (Xo i.l).XF i.c, (y ≫ pullback.snd _ _ = spMap f ∧ IsFibre (Y i).oF y o) ∧
      y' ≫ (Y i').j ≫ τ = y ≫ (Y i).j := by
  obtain ⟨b, π', r, hb, e₁, e₂, -, e₃, h₁, h₂⟩ := h
  obtain ⟨ν, hν⟩ := exists_sab_square e₃ (Y i).m (Y i').m mu
  refine ⟨y' ≫ r, ⟨?_, isFibre_lower hl ν
    (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₁ a)))
    (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₂ a))) ho⟩,
    (congrArg (y' ≫ ·) e₃).trans (Category.assoc _ _ _).symm⟩
  obtain ⟨g, hg⟩ : ∃ g : i.c.F →+* K, (y' ≫ r) ≫ pullback.snd _ _ = spMap g :=
    ⟨(Spec.preimage ((y' ≫ r) ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have e₄ : spMap (g.comp (i.c.V W).subtype) = spMap ((f'.comp (i'.c.V W).subtype).comp b) := by
    rw [spMap_comp, spMap_comp, spMap_comp, ← hg, ← hy]
    exact base_square (j_s (Y i)) (j_s (Y i')) e₁ e₂ e₃ y'
  exact hg.trans (congrArg spMap (ringHom_ext_val (i.c.V W) fun x =>
    (DFunLike.congr_fun (spMap_inj e₄) x).trans (hf _ _ (hb x))))

/- English proof (translation)
Introduce `E _ _ _ H D Xo p W Y hp hW hpq C i₁ P₁`. Establish `laws : Out.Laws` using `GlobalTheory.abelianSchemeLaws_all.1`. Take `⟨j₀, hj, hj'⟩` from `GlobalTheory.T.chart_embedding_holds p W i₁.c.F C P₁.fK hp hW i₁.c.fin fun x hx => (DFunLike.congr_fun P₁.compat ⟨x, hx⟩ ▸ (P₁.alg ⟨x, hx⟩).2 : ‖(P₁.fK.comp (i₁.c.V W).subtype) ⟨x, hx⟩‖ ≤ 1)`. Establish `halg : ∀ (i : Idx H p) (x : i.c.F), (x : ℂ) ∈ algebraicClosure ℚ ℂ` using `fun i x => by`. Use `i.c.fin` as an intermediate fact.

Conclude with `mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom i.c.F.val)`. Set `f : ∀ i : Idx H p, i.c.F →+* ↥C.S` to `fun i => j₀.comp ((i.c.F.val : i.c.F →+* ℂ).codRestrict (algebraicClosure ℚ ℂ) (halg i))`. Establish `hf : ∀ i x, f i x = j₀ ⟨x, halg i x⟩` using `fun _ _ => rfl`. Establish `hf₁ : f i₁ = P₁.fK` using `RingHom.ext fun x => hj x _`. Establish `hz : ∀ n, zeta n ∈ algebraicClosure ℚ ℂ` using `fun n => by`.

Break down `n.eq_zero_or_pos with rfl | hn` into its components or cases. Simplify `one_mem _` using `[zeta]`. Conclude with `mem_algebraicClosure_iff.2 ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top.isAlgebraic`. Set `z₀ : ℕ → (algebraicClosure ℚ ℂ)ˣ` to `fun n => Units.mk0 ⟨zeta n, hz n⟩ fun h => Complex.exp_ne_zero _ (congrArg Subtype.val h)`. Set `u : (algebraicClosure ℚ ℂ)ˣ →* ℂˣ` to `Units.map (algebraicClosure ℚ ℂ).val.toRingHom.toMonoidHom`.

Establish `hu : Function.Injective u` using `Units.map_injective Subtype.val_injective`. Establish `hu₀ : ∀ n, u (z₀ n) = ValInh.zetaU n` using `fun n => Units.ext rfl`. Set `z : ℕ → (↥C.S)ˣ` to `fun n => Units.map j₀.toMonoidHom (z₀ n)`. Take `⟨o, ho, hc⟩` from `exists_isFibre (Y i₁).oF P₁.y`. Take `⟨hρ, hζ⟩` from `hc (P₁.fK.comp (IntermediateField.inclusion i₁.c.le).toRingHom) (by`.

Rewrite using `[pullback.condition, ← Category.assoc, P₁.y_over, spMap_comp])`. Take `⟨I, hI, hA, hM⟩` from `GlobalTheory.T.chart_roots_holds E H D i₁.l _ _ _ _ o.I z hpq (fun n hn => (IsPrimitiveRoot.of_map_of_injective (f := u) (hu₀ n ▸ ValInh.zetaU_prim n hn) hu).map_of_injective (Units.map_injective j₀.injective)) (fun n m hn hm => by`. Rewrite using `[← map_pow]`. Conclude with `congrArg _ (hu (by rw [map_pow, hu₀, hu₀, ValInh.zetaU_pow n m hn hm])))`. Use the proof step `(Units.ext (Eq.trans (by rw [← hf₁]; rfl) hζ.symm))`.

Set `o' : Full D ↥C.S` to `{ o with I := I }`. Establish `ho' : IsFibre (Y i₁).oF P₁.y o'`. Take `⟨φ, g₁, g₂, g₃, g₄, g₅⟩` from `ho`. Conclude with `⟨φ, g₁, g₂, g₃, fun v => (congrArg (fun q => q.left ≫ φ) (hA v)).trans (g₄ v), fun v hv => (congrArg (fun q => q.left ≫ φ) (hM v hv)).trans (g₅ v hv)⟩`. Establish `hpt : ∀ i : Idx H p, ∃! y : Sp ↥C.S ⟶ (Xo i.l).XF i.c, y ≫ pullback.snd _ _ = spMap (f i) ∧ IsFibre (Y i).oF y o'` using `fun i => existsUnique_point laws (Y i) (f i) o' (fun r hr => hρ.trans (by rw [← hf₁]; exact congrArg j₀ (Subtype.ext hr.symm))) (fun r hr => (congrArg Units.val (hI _ i.l.A_pos)).trans (congrArg j₀ (Subtype.ext hr.symm)))`.

Use `choose y hy hy' using hpt`. Use `choose P hP hP' using fun i => exists_ptC (Y i) C (f i) (fun x => hj' _ x.2) (y i) (hy i).1`. Use `⟨P, ptC_ext ((hP i₁).trans hf₁) ((hP' i₁).trans (hy' i₁ _ ⟨hf₁ ▸ P₁.y_over, ho'⟩).symm), fun i i' τ mu hl h => base_ext i _ _ ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hw'⟩` from `exists_lower hl h (f i) (f i') (fun x x' e => congrArg j₀ (Subtype.ext e)) (hy i').1 (hy i').2`. Rewrite using `[← Category.assoc, (P i').ext, (P i).ext, hP', hP', Category.assoc, hw', hy' i w hw]`.
-/
theorem tower : TowerSt := by
  intro E _ _ _ H D Xo p W Y hp hW hpq C i₁ P₁
  have laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨j₀, hj, hj'⟩ := GlobalTheory.T.chart_embedding_holds p W i₁.c.F C P₁.fK hp hW i₁.c.fin fun x hx =>
    (DFunLike.congr_fun P₁.compat ⟨x, hx⟩ ▸ (P₁.alg ⟨x, hx⟩).2 : ‖(P₁.fK.comp (i₁.c.V W).subtype) ⟨x, hx⟩‖ ≤ 1)
  have halg : ∀ (i : Idx H p) (x : i.c.F), (x : ℂ) ∈ algebraicClosure ℚ ℂ := fun i x => by
    have := i.c.fin
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom i.c.F.val)
  let f : ∀ i : Idx H p, i.c.F →+* ↥C.S := fun i =>
    j₀.comp ((i.c.F.val : i.c.F →+* ℂ).codRestrict (algebraicClosure ℚ ℂ) (halg i))
  have hf : ∀ i x, f i x = j₀ ⟨x, halg i x⟩ := fun _ _ => rfl
  have hf₁ : f i₁ = P₁.fK := RingHom.ext fun x => hj x _
  have hz : ∀ n, zeta n ∈ algebraicClosure ℚ ℂ := fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa [zeta] using one_mem _
    · exact mem_algebraicClosure_iff.2
        ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top.isAlgebraic
  let z₀ : ℕ → (algebraicClosure ℚ ℂ)ˣ := fun n =>
    Units.mk0 ⟨zeta n, hz n⟩ fun h => Complex.exp_ne_zero _ (congrArg Subtype.val h)
  let u : (algebraicClosure ℚ ℂ)ˣ →* ℂˣ := Units.map (algebraicClosure ℚ ℂ).val.toRingHom.toMonoidHom
  have hu : Function.Injective u := Units.map_injective Subtype.val_injective
  have hu₀ : ∀ n, u (z₀ n) = ValInh.zetaU n := fun n => Units.ext rfl
  let z : ℕ → (↥C.S)ˣ := fun n => Units.map j₀.toMonoidHom (z₀ n)
  obtain ⟨o, ho, hc⟩ := exists_isFibre (Y i₁).oF P₁.y
  obtain ⟨hρ, hζ⟩ := hc (P₁.fK.comp (IntermediateField.inclusion i₁.c.le).toRingHom) (by
    rw [pullback.condition, ← Category.assoc, P₁.y_over, spMap_comp])
  obtain ⟨I, hI, hA, hM⟩ := GlobalTheory.T.chart_roots_holds E H D i₁.l _ _ _ _ o.I z hpq
    (fun n hn => (IsPrimitiveRoot.of_map_of_injective (f := u) (hu₀ n ▸ ValInh.zetaU_prim n hn) hu).map_of_injective
      (Units.map_injective j₀.injective))
    (fun n m hn hm => by
      rw [← map_pow]
      exact congrArg _ (hu (by rw [map_pow, hu₀, hu₀, ValInh.zetaU_pow n m hn hm])))
    (Units.ext (Eq.trans (by rw [← hf₁]; rfl) hζ.symm))
  let o' : Full D ↥C.S := { o with I := I }
  have ho' : IsFibre (Y i₁).oF P₁.y o' := by
    obtain ⟨φ, g₁, g₂, g₃, g₄, g₅⟩ := ho
    exact ⟨φ, g₁, g₂, g₃, fun v => (congrArg (fun q => q.left ≫ φ) (hA v)).trans (g₄ v),
      fun v hv => (congrArg (fun q => q.left ≫ φ) (hM v hv)).trans (g₅ v hv)⟩
  have hpt : ∀ i : Idx H p, ∃! y : Sp ↥C.S ⟶ (Xo i.l).XF i.c,
      y ≫ pullback.snd _ _ = spMap (f i) ∧ IsFibre (Y i).oF y o' := fun i =>
    existsUnique_point laws (Y i) (f i) o'
      (fun r hr => hρ.trans (by rw [← hf₁]; exact congrArg j₀ (Subtype.ext hr.symm)))
      (fun r hr => (congrArg Units.val (hI _ i.l.A_pos)).trans (congrArg j₀ (Subtype.ext hr.symm)))
  choose y hy hy' using hpt
  choose P hP hP' using fun i => exists_ptC (Y i) C (f i) (fun x => hj' _ x.2) (y i) (hy i).1
  refine ⟨P, ptC_ext ((hP i₁).trans hf₁) ((hP' i₁).trans (hy' i₁ _ ⟨hf₁ ▸ P₁.y_over, ho'⟩).symm),
    fun i i' τ mu hl h => base_ext i _ _ ?_⟩
  obtain ⟨w, hw, hw'⟩ := exists_lower hl h (f i) (f i') (fun x x' e => congrArg j₀ (Subtype.ext e)) (hy i').1 (hy i').2
  rw [← Category.assoc, (P i').ext, (P i).ext, hP', hP', Category.assoc, hw', hy' i w hw]

end GlobalTheory.LocM.Tower
