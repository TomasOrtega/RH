import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourUniq

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

def Yk (L Y : AddSubgroup W) (k : ℕ) : AddSubgroup W := Y ⊓ L.comap (nsmulAddMonoidHom k)

/- English proof (translation)
Simplify using `[Yk, AddSubgroup.mem_inf, AddSubgroup.mem_comap]`.
-/
theorem mem_Yk {L Y : AddSubgroup W} {k : ℕ} {y : W} : y ∈ Yk L Y k ↔ y ∈ Y ∧ k • y ∈ L := by
  simp [Yk, AddSubgroup.mem_inf, AddSubgroup.mem_comap]

abbrev Ik (L Y : AddSubgroup W) (k : ℕ) : Type _ := ↥(Yk L Y k) ⧸ (smulSub k (L ⊓ Y)).addSubgroupOf (Yk L Y k)

/- English proof (translation)
Set `f : Ik L Y k → Qt (k * k) (L ⊓ Y)` to `fun q => QuotientAddGroup.mk ⟨k • ((q.out : ↥(Yk L Y k)) : W), AddSubgroup.mem_inf.2 ⟨(mem_Yk.1 (q.out : ↥(Yk L Y k)).2).2, Y.nsmul_mem (mem_Yk.1 (q.out : ↥(Yk L Y k)).2).1 k⟩⟩`. Use `Finite.of_injective f fun q q' h => ?_` and prove the remaining obligations. Establish `h1` using `QuotientAddGroup.eq.1 h`. Rewrite `h1` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨u, hu, hux⟩` from `mem_smulSub.1 h1`.

Establish `h2 : k • (-((q.out : ↥(Yk L Y k)) : W) + ((q'.out : ↥(Yk L Y k)) : W) - k • u) = 0`. Rewrite using `[smul_sub, smul_add, smul_neg, smul_smul, hux]`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Normalize the expressions using the abelian group laws. Establish `h3` using `sub_eq_zero.1 (htf _ h2)`.

Use `(QuotientAddGroup.out_eq' q).symm.trans ((QuotientAddGroup.eq.2 ?_).trans (QuotientAddGroup.out_eq' q'))` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Rewrite using `[h3]`. Conclude with `mem_smulSub.2 ⟨u, hu, rfl⟩`.
-/
theorem Ik_finite {L Y : AddSubgroup W} {k : ℕ} [Finite (Qt (k * k) (L ⊓ Y))]
    (htf : ∀ t : W, k • t = 0 → t = 0) : Finite (Ik L Y k) := by
  let f : Ik L Y k → Qt (k * k) (L ⊓ Y) := fun q => QuotientAddGroup.mk
    ⟨k • ((q.out : ↥(Yk L Y k)) : W), AddSubgroup.mem_inf.2 ⟨(mem_Yk.1 (q.out : ↥(Yk L Y k)).2).2,
      Y.nsmul_mem (mem_Yk.1 (q.out : ↥(Yk L Y k)).2).1 k⟩⟩
  refine Finite.of_injective f fun q q' h => ?_
  have h1 := QuotientAddGroup.eq.1 h
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h1
  have h2 : k • (-((q.out : ↥(Yk L Y k)) : W) + ((q'.out : ↥(Yk L Y k)) : W) - k • u) = 0 := by
    rw [smul_sub, smul_add, smul_neg, smul_smul, hux]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  have h3 := sub_eq_zero.1 (htf _ h2)
  refine (QuotientAddGroup.out_eq' q).symm.trans ((QuotientAddGroup.eq.2 ?_).trans (QuotientAddGroup.out_eq' q'))
  rw [AddSubgroup.mem_addSubgroupOf]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
  rw [h3]
  exact mem_smulSub.2 ⟨u, hu, rfl⟩

def IsLev (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : Prop :=
  (∀ u ∈ L ⊓ X, ρ (k • u) G = G) ∧ ∀ u ∈ L ⊓ Y, ρ (k • u) G = G

/- English proof (translation)
Use `⟨fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_smul]`. Conclude with `h.1 _ (AddSubgroup.nsmul_mem _ hu j)`. Rewrite using `[← smul_smul]`. Conclude with `h.2 _ (AddSubgroup.nsmul_mem _ hu j)`.
-/
theorem IsLev.mul {ρ : W → Module.End ℂ V} {L X Y : AddSubgroup W} {k : ℕ} {G : V} (h : IsLev ρ L X Y k G) (j : ℕ) :
    IsLev ρ L X Y (k * j) G := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [← smul_smul]
    exact h.1 _ (AddSubgroup.nsmul_mem _ hu j)
  · rw [← smul_smul]
    exact h.2 _ (AddSubgroup.nsmul_mem _ hu j)

def piK (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : V :=
  ∑ᶠ b : Qt k (L ⊓ X), ρ ((b.out : ↥(L ⊓ X)) : W) (∑ᶠ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) G)

/- English proof (translation)
Establish `h` using `QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk z : Ik L Y k))`. Rewrite `h` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨v, hv, hvx⟩` from `mem_smulSub.1 h`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[hvx]`.

Use `push_cast`. Normalize the expressions using the abelian group laws.
-/
theorem Ik_out_mk {L Y : AddSubgroup W} {k : ℕ} (z : Yk L Y k) :
    ∃ v ∈ L ⊓ Y, ((((QuotientAddGroup.mk z : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v = (z : W) := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk z : Ik L Y k))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 h
  refine ⟨v, hv, ?_⟩
  rw [hvx]
  push_cast
  abel

section PiK

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}

/- English proof (translation)
Use `haveI := Fintype.ofFinite (Qt k (L ⊓ X))`. Use `haveI := Fintype.ofFinite (Ik L Y k)`. Simplify using `only [piK, finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib]`.
-/
theorem piK_add {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G + H) = piK ρ L X Y k G + piK ρ L X Y k H := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib]

/- English proof (translation)
Use `haveI := Fintype.ofFinite (Qt k (L ⊓ X))`. Use `haveI := Fintype.ofFinite (Ik L Y k)`. Simplify using `only [piK, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]`.
-/
theorem piK_smul {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (c : ℂ) (G : V) :
    piK ρ L X Y k (c • G) = c • piK ρ L X Y k G := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]

/- English proof (translation)
Use `haveI := Fintype.ofFinite (Qt k (L ⊓ X))`. Use `haveI := Fintype.ofFinite (Ik L Y k)`. Simplify using `only [piK, finsum_eq_sum_of_fintype, map_sub, Finset.sum_sub_distrib]`.
-/
theorem piK_sub {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G - H) = piK ρ L X Y k G - piK ρ L X Y k H := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Use `letI := Fintype.ofFinite (Ik L Y k)`. Unfold `piK`. Use `congr 1`. Use function extensionality and compare the values at `b`. Use `congr 1`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Set `m : Ik L Y k` to `QuotientAddGroup.mk ⟨u, hu⟩`. Establish `huY : u ∈ Y` using `(mem_Yk.1 hu).1`. Establish `key : ∀ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) (ρ u G) = ρ (((y + m).out : ↥(Yk L Y k)) : W) G`. Introduce `y`.

Establish `hyY : ((y.out : ↥(Yk L Y k)) : W) ∈ Y` using `(mem_Yk.1 (y.out : ↥(Yk L Y k)).2).1`. Establish `h1 : y + m = QuotientAddGroup.mk (y.out + ⟨u, hu⟩)`. Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Take `⟨v, hv, hout⟩` from `Ik_out_mk (L := L) (Y := Y) (k := k) (y.out + ⟨u, hu⟩)`. Rewrite using `[h1]`.

Establish `hoY : ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) ∈ Y` using `(mem_Yk.1 ((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out.2).1`. Establish `hkvY : k • v ∈ Y` using `Y.nsmul_mem (AddSubgroup.mem_inf.1 hv).2 k`. Rewrite using `[← Module.End.mul_apply, ← hY _ hyY _ huY]`. Establish `h2 : ((y.out : ↥(Yk L Y k)) : W) + u = ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v`. Rewrite using `[hout]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h2, hY _ hoY _ hkvY, Module.End.mul_apply, hG v hv]`. Rewrite using `[Finset.sum_congr rfl fun y _ => key y]`. Conclude with `Fintype.sum_equiv (Equiv.addRight m) _ _ (fun _ => rfl)`.
-/
theorem piK_shift (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y') {k : ℕ} [Finite (Ik L Y k)]
    {u : W} (hu : u ∈ Yk L Y k) {G : V} (hG : ∀ v ∈ L ⊓ Y, ρ (k • v) G = G) :
    piK ρ L X Y k (ρ u G) = piK ρ L X Y k G := by
  classical
  letI := Fintype.ofFinite (Ik L Y k)
  unfold piK
  congr 1
  funext b
  congr 1
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let m : Ik L Y k := QuotientAddGroup.mk ⟨u, hu⟩
  have huY : u ∈ Y := (mem_Yk.1 hu).1
  have key : ∀ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) (ρ u G) = ρ (((y + m).out : ↥(Yk L Y k)) : W) G := by
    intro y
    have hyY : ((y.out : ↥(Yk L Y k)) : W) ∈ Y := (mem_Yk.1 (y.out : ↥(Yk L Y k)).2).1
    have h1 : y + m = QuotientAddGroup.mk (y.out + ⟨u, hu⟩) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    obtain ⟨v, hv, hout⟩ := Ik_out_mk (L := L) (Y := Y) (k := k) (y.out + ⟨u, hu⟩)
    rw [h1]
    have hoY : ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) ∈ Y :=
      (mem_Yk.1 ((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out.2).1
    have hkvY : k • v ∈ Y := Y.nsmul_mem (AddSubgroup.mem_inf.1 hv).2 k
    rw [← Module.End.mul_apply, ← hY _ hyY _ huY]
    have h2 : ((y.out : ↥(Yk L Y k)) : W) + u =
        ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v := by
      rw [hout]
      push_cast
      rfl
    rw [h2, hY _ hoY _ hkvY, Module.End.mul_apply, hG v hv]
  rw [Finset.sum_congr rfl fun y _ => key y]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun _ => rfl)

end PiK

section Vac

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχl hχr hχ0 hLL hdY in
open Classical in

/- English proof (translation)
Establish `hy'` using `mem_Yk.1 hy`. Use `split_ifs with hyL`. Establish `h1 : ∀ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 1` using `fun b => hLL _ (b.out : ↥(L ⊓ X)).2 y (AddSubgroup.mem_inf.2 ⟨hyL, hy'.1⟩)`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Establish `hne : ¬ ∀ x ∈ L ⊓ X, χ x y = 1` using `fun hall => hyL (hdY y hy'.1 hall) push_neg at hne`.

Take `⟨u, hu, hχu⟩` from `hne`. Set `m : Qt k (L ⊓ X)` to `QuotientAddGroup.mk ⟨u, hu⟩`. Establish `hkey : ∀ b : Qt k (L ⊓ X), χ (((b + m).out : ↥(L ⊓ X)) : W) y = χ ((b.out : ↥(L ⊓ X)) : W) y * χ u y`. Introduce `b`. Establish `h1 : b + m = QuotientAddGroup.mk (b.out + ⟨u, hu⟩)`.

Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Take `⟨v, hv, hout⟩` from `out_mk k (L ⊓ X) (b.out + ⟨u, hu⟩)`. Rewrite using `[h1]`. Establish `h2 : (((QuotientAddGroup.mk (b.out + ⟨u, hu⟩) : Qt k (L ⊓ X)).out : ↥(L ⊓ X)) : W) = ((b.out : ↥(L ⊓ X)) : W) + u + -(k • v)`. Rewrite using `[eq_sub_of_add_eq hout]`.

Use `push_cast`. Normalize the expressions using the abelian group laws. Rewrite using `[h2, hχl, hχl, chi_neg_left hχl hχ0, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0, hLL v hv _ (AddSubgroup.mem_inf.2 ⟨hy'.2, Y.nsmul_mem hy'.1 k⟩), inv_one, mul_one]`. Establish `hshift : ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y) * χ u y`. Rewrite using `[Finset.sum_mul]`.

Rewrite using `[← Fintype.sum_equiv (Equiv.addRight m) (fun b => χ (((b + m).out : ↥(L ⊓ X)) : W) y) (fun b => χ ((b.out : ↥(L ⊓ X)) : W) y) (fun b => rfl)]`. Conclude with `Finset.sum_congr rfl fun b _ => hkey b`. Establish `hz : (1 - χ u y) * ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 0`. Take the linear combination `hshift`. Break down `mul_eq_zero.1 hz with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.1 h).symm hχu`. Conclude with `h`.
-/
theorem chi_sum_X {k : ℕ} [Fintype (Qt k (L ⊓ X))] {y : W} (hy : y ∈ Yk L Y k) :
    ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
      if y ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0 := by
  classical
  have hy' := mem_Yk.1 hy
  split_ifs with hyL
  · have h1 : ∀ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 1 := fun b =>
      hLL _ (b.out : ↥(L ⊓ X)).2 y (AddSubgroup.mem_inf.2 ⟨hyL, hy'.1⟩)
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · have hne : ¬ ∀ x ∈ L ⊓ X, χ x y = 1 := fun hall => hyL (hdY y hy'.1 hall)
    push_neg at hne
    obtain ⟨u, hu, hχu⟩ := hne
    let m : Qt k (L ⊓ X) := QuotientAddGroup.mk ⟨u, hu⟩
    have hkey : ∀ b : Qt k (L ⊓ X), χ (((b + m).out : ↥(L ⊓ X)) : W) y = χ ((b.out : ↥(L ⊓ X)) : W) y * χ u y := by
      intro b
      have h1 : b + m = QuotientAddGroup.mk (b.out + ⟨u, hu⟩) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      obtain ⟨v, hv, hout⟩ := out_mk k (L ⊓ X) (b.out + ⟨u, hu⟩)
      rw [h1]
      have h2 : (((QuotientAddGroup.mk (b.out + ⟨u, hu⟩) : Qt k (L ⊓ X)).out : ↥(L ⊓ X)) : W) =
          ((b.out : ↥(L ⊓ X)) : W) + u + -(k • v) := by
        rw [eq_sub_of_add_eq hout]; push_cast; abel
      rw [h2, hχl, hχl, chi_neg_left hχl hχ0, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
        hLL v hv _ (AddSubgroup.mem_inf.2 ⟨hy'.2, Y.nsmul_mem hy'.1 k⟩), inv_one, mul_one]
    have hshift : ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
        (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y) * χ u y := by
      rw [Finset.sum_mul]
      rw [← Fintype.sum_equiv (Equiv.addRight m) (fun b => χ (((b + m).out : ↥(L ⊓ X)) : W) y)
        (fun b => χ ((b.out : ↥(L ⊓ X)) : W) y) (fun b => rfl)]
      exact Finset.sum_congr rfl fun b _ => hkey b
    have hz : (1 - χ u y) * ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 0 := by
      linear_combination hshift
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd (sub_eq_zero.1 h).symm hχu
    · exact h

include hXY hχl hχr hχ0 hLL hdY in

/- English proof (translation)
Use `letI := Fintype.ofFinite (Qt k (L ⊓ X))`. Use `letI := Fintype.ofFinite (Ik L Y k)`. Establish `hyk : ∀ y : Ik L Y k, ((y.out : ↥(Yk L Y k)) : W) ∈ Yk L Y k` using `fun y => (y.out : ↥(Yk L Y k)).2`. Establish `hterm : ∀ (b : Qt k (L ⊓ X)) (y : Ik L Y k), ρ ((b.out : ↥(L ⊓ X)) : W) (ρ ((y.out : ↥(Yk L Y k)) : W) w) = χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W) • ρ ((y.out : ↥(Yk L Y k)) : W) w`. Introduce `b y`.

Use `congrArg (fun T : Module.End ℂ V => T w) (hXY _ (AddSubgroup.mem_inf.1 (b.out : ↥(L ⊓ X)).2).2 _ (mem_Yk.1 (hyk y)).1)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite using `[this, hwX _ (b.out : ↥(L ⊓ X)).2]`. Establish `e1 : piK ρ L X Y k w = ∑ y : Ik L Y k, (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W)) • ρ ((y.out : ↥(Yk L Y k)) : W) w`. Unfold `piK`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Simplify using `only [map_sum, hterm, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Rewrite using `[e1]`. Simplify using `only [chi_sum_X hχl hχr hχ0 hLL hdY (hyk _)]`.

Establish `e2 : ∀ y : Ik L Y k, (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) • ρ ((y.out : ↥(Yk L Y k)) : W) w = (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) • w`. Introduce `y`. Use `split_ifs with h`. Rewrite using `[hwY _ (AddSubgroup.mem_inf.2 ⟨h, (mem_Yk.1 (hyk y)).1⟩)]`. Rewrite using `[zero_smul, zero_smul]`.

Simplify using `only [e2, ← Finset.sum_smul]`. Use `⟨_, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Use `mul_ne_zero ?_ (by exact_mod_cast Fintype.card_ne_zero)` and prove the remaining obligations. Establish `h0 : (0 : Ik L Y k) ∈ Finset.univ.filter (fun y : Ik L Y k => ((y.out : ↥(Yk L Y k)) : W) ∈ L)`.

Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `(QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : Ik L Y k))` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨v, hv, hvx⟩` from `mem_smulSub.1 this`.

Rewrite using `[← hvx]`. Conclude with `L.nsmul_mem (AddSubgroup.mem_inf.1 hv).1 k`. Conclude with `(Finset.card_pos.2 ⟨_, h0⟩).ne'` after adjusting the coercions.
-/
theorem piK_vac {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] {w : V} (hwX : ∀ u ∈ L ⊓ X, ρ u w = w)
    (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w) : ∃ c : ℂ, c ≠ 0 ∧ piK ρ L X Y k w = c • w := by
  classical
  letI := Fintype.ofFinite (Qt k (L ⊓ X))
  letI := Fintype.ofFinite (Ik L Y k)
  have hyk : ∀ y : Ik L Y k, ((y.out : ↥(Yk L Y k)) : W) ∈ Yk L Y k := fun y => (y.out : ↥(Yk L Y k)).2
  have hterm : ∀ (b : Qt k (L ⊓ X)) (y : Ik L Y k), ρ ((b.out : ↥(L ⊓ X)) : W) (ρ ((y.out : ↥(Yk L Y k)) : W) w) =
      χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W) • ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    intro b y
    have := congrArg (fun T : Module.End ℂ V => T w)
      (hXY _ (AddSubgroup.mem_inf.1 (b.out : ↥(L ⊓ X)).2).2 _ (mem_Yk.1 (hyk y)).1)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hwX _ (b.out : ↥(L ⊓ X)).2]
  have e1 : piK ρ L X Y k w = ∑ y : Ik L Y k,
      (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W)) •
        ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    unfold piK
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [map_sum, hterm, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  simp only [chi_sum_X hχl hχr hχ0 hLL hdY (hyk _)]
  have e2 : ∀ y : Ik L Y k, (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) •
      ρ ((y.out : ↥(Yk L Y k)) : W) w =
      (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) • w := by
    intro y
    split_ifs with h
    · rw [hwY _ (AddSubgroup.mem_inf.2 ⟨h, (mem_Yk.1 (hyk y)).1⟩)]
    · rw [zero_smul, zero_smul]
  simp only [e2, ← Finset.sum_smul]
  refine ⟨_, ?_, rfl⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ (by exact_mod_cast Fintype.card_ne_zero)
  have h0 : (0 : Ik L Y k) ∈ Finset.univ.filter (fun y : Ik L Y k => ((y.out : ↥(Yk L Y k)) : W) ∈ L) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : Ik L Y k))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 this
    rw [← hvx]
    exact L.nsmul_mem (AddSubgroup.mem_inf.1 hv).1 k
  exact_mod_cast (Finset.card_pos.2 ⟨_, h0⟩).ne'

include hY hXY hχl hχr hχ0 hLL in

/- English proof (translation)
Establish `c0 : ∀ y, χ 0 y = 1` using `fun y => by`. Establish `h` using `hχl 0 0 y`. Rewrite `h` using `[add_zero]`. Conclude with `mul_right_cancel₀ (hχ0 0 y) (by rw [one_mul]; exact h.symm)`. Establish `c0' : ∀ t, χ t 0 = 1` using `fun t => by`.

Establish `h` using `hχr t 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_right_cancel₀ (hχ0 t 0) (by rw [one_mul]; exact h.symm)`. Establish `cl : ∀ (n : ℕ) t y, χ (n • t) y = χ t y ^ n`. Introduce `n t y`.

Proceed by induction on `n with`. Consider the case `zero => simp [c0]`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`. Establish `cr : ∀ (n : ℕ) t y, χ t (n • y) = χ t y ^ n`. Introduce `n t y`.

Proceed by induction on `n with`. Consider the case `zero => simp [c0']`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`. Use `⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hx : ρ ((k * m) • v) G = G`.

Rewrite using `[← smul_smul]`. Conclude with `hG.1 _ (AddSubgroup.nsmul_mem _ hv m)`. Establish `hmuY : m • u ∈ L ⊓ Y` using `AddSubgroup.mem_inf.2 ⟨hmu, AddSubgroup.nsmul_mem _ hu m⟩`. Establish `hchi : χ ((k * m) • v) u = 1`. Rewrite using `[cl, mul_comm, pow_mul, ← cr, hLL v hv _ hmuY, one_pow]`.

Establish `hc` using `hXY ((k * m) • v) (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _) u hu`. Combine the equalities or inequalities in the displayed calculation. Establish `hx : ρ ((k * m) • v) G = G`. Rewrite using `[← smul_smul]`. Conclude with `hG.2 _ (AddSubgroup.nsmul_mem _ hv m)`.

Establish `hy : (k * m) • v ∈ Y` using `AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _`. Establish `comm : ρ ((k * m) • v) * ρ u = ρ u * ρ ((k * m) • v)`. Rewrite using `[← hY _ hy _ hu, ← hY _ hu _ hy, add_comm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsLev.Heisenberg₂ {k m : ℕ} {G : V} (hG : IsLev ρ L X Y k G) {u : W} (hu : u ∈ Y) (hmu : m • u ∈ L) :
    IsLev ρ L X Y (k * m) (ρ u G) := by
  have c0 : ∀ y, χ 0 y = 1 := fun y => by
    have h := hχl 0 0 y
    rw [add_zero] at h
    exact mul_right_cancel₀ (hχ0 0 y) (by rw [one_mul]; exact h.symm)
  have c0' : ∀ t, χ t 0 = 1 := fun t => by
    have h := hχr t 0 0
    rw [add_zero] at h
    exact mul_right_cancel₀ (hχ0 t 0) (by rw [one_mul]; exact h.symm)
  have cl : ∀ (n : ℕ) t y, χ (n • t) y = χ t y ^ n := by
    intro n t y
    induction n with
    | zero => simp [c0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have cr : ∀ (n : ℕ) t y, χ t (n • y) = χ t y ^ n := by
    intro n t y
    induction n with
    | zero => simp [c0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hx : ρ ((k * m) • v) G = G := by
      rw [← smul_smul]
      exact hG.1 _ (AddSubgroup.nsmul_mem _ hv m)
    have hmuY : m • u ∈ L ⊓ Y := AddSubgroup.mem_inf.2 ⟨hmu, AddSubgroup.nsmul_mem _ hu m⟩
    have hchi : χ ((k * m) • v) u = 1 := by
      rw [cl, mul_comm, pow_mul, ← cr, hLL v hv _ hmuY, one_pow]
    have hc := hXY ((k * m) • v) (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _) u hu
    calc ρ ((k * m) • v) (ρ u G) = (ρ ((k * m) • v) * ρ u) G := rfl
      _ = (χ ((k * m) • v) u • (ρ u * ρ ((k * m) • v))) G := by rw [hc]
      _ = ρ u G := by rw [hchi, one_smul, Module.End.mul_apply, hx]
  · have hx : ρ ((k * m) • v) G = G := by
      rw [← smul_smul]
      exact hG.2 _ (AddSubgroup.nsmul_mem _ hv m)
    have hy : (k * m) • v ∈ Y := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _
    have comm : ρ ((k * m) • v) * ρ u = ρ u * ρ ((k * m) • v) := by
      rw [← hY _ hy _ hu, ← hY _ hu _ hy, add_comm]
    calc ρ ((k * m) • v) (ρ u G) = (ρ ((k * m) • v) * ρ u) G := rfl
      _ = (ρ u * ρ ((k * m) • v)) G := by rw [comm]
      _ = ρ u G := by rw [Module.End.mul_apply, hx]

include hY hXY hχl hχr hχ0 hLL hdY hfinX hfinY htf in

/- English proof (translation)
Take `⟨n, f, g, hsum⟩` from `Submodule.mem_span_set'.1 hw`. Use `choose u hu G hG hg using fun i => (g i).2`. Use `choose kf hkf0 hkf using fun i => hlev (G i) (hG i)`. Use `choose mf hmf0 hmf using fun i => hoY (u i) (hu i)`. Use `set K := ∏ i, (kf i * mf i) with hKdef`.

Establish `hK0 : 0 < K` using `Finset.prod_pos fun i _ => Nat.mul_pos (hkf0 i) (hmf0 i)`. Establish `hdiv : ∀ i, kf i * mf i ∣ K` using `fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Use `haveI := hfinX K hK0`. Use `haveI := hfinY (K * K) (Nat.mul_pos hK0 hK0)`. Use `haveI : Finite (Ik L Y K) := Ik_finite (htf K hK0)`.

Establish `hzero : ∀ i, piK ρ L X Y K (ρ (u i) (G i) - G i) = 0`. Introduce `i`. Take `⟨c, hc⟩` from `hdiv i`. Establish `hGK : IsLev ρ L X Y K (G i)`. Use `(hkf i).mul (mf i * c)` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← hc]`. Then use the resulting hypothesis. Establish `huK : u i ∈ Yk L Y K` using `mem_Yk.2 ⟨hu i, by`. Rewrite using `[hc, mul_comm (kf i) (mf i), mul_assoc, mul_comm, ← smul_smul]`. Conclude with `L.nsmul_mem (hmf i) _⟩`. Rewrite using `[piK_sub, piK_shift hY huK hGK.2, sub_self]`.

Establish `hpw : piK ρ L X Y K w = 0`. Rewrite using `[← hsum]`. Establish `: ∀ s : Finset (Fin n), piK ρ L X Y K (∑ i ∈ s, f i • ((g i : {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : V)) = 0`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Rewrite using `[Finset.sum_empty]`. Use `piK_smul (ρ := ρ) (L := L) (X := X) (Y := Y) (k := K) (0 : ℂ) (0 : V)` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis. Consider the case `insert i s his ih`.

Rewrite using `[Finset.sum_insert his, piK_add, ih, add_zero, piK_smul, hg i, hzero i, smul_zero]`. Conclude with `this Finset.univ`. Take `⟨c, hc0, hc⟩` from `piK_vac hXY hχl hχr hχ0 hLL hdY (k := K) hwX hwY`. Rewrite `hpw` using `[hc]`. Conclude with `(smul_eq_zero.1 hpw).resolve_left hc0`.
-/
theorem vac_eq_zero_of_mem_span (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L) (Θ : Set V)
    (hlev : ∀ G ∈ Θ, ∃ k : ℕ, 0 < k ∧ IsLev ρ L X Y k G) {w : V}
    (hwX : ∀ u ∈ L ⊓ X, ρ u w = w) (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w)
    (hw : w ∈ Submodule.span ℂ {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : w = 0 := by
  classical
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hw
  choose u hu G hG hg using fun i => (g i).2
  choose kf hkf0 hkf using fun i => hlev (G i) (hG i)
  choose mf hmf0 hmf using fun i => hoY (u i) (hu i)
  set K := ∏ i, (kf i * mf i) with hKdef
  have hK0 : 0 < K := Finset.prod_pos fun i _ => Nat.mul_pos (hkf0 i) (hmf0 i)
  have hdiv : ∀ i, kf i * mf i ∣ K := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  haveI := hfinX K hK0
  haveI := hfinY (K * K) (Nat.mul_pos hK0 hK0)
  haveI : Finite (Ik L Y K) := Ik_finite (htf K hK0)
  have hzero : ∀ i, piK ρ L X Y K (ρ (u i) (G i) - G i) = 0 := by
    intro i
    obtain ⟨c, hc⟩ := hdiv i
    have hGK : IsLev ρ L X Y K (G i) := by
      have := (hkf i).mul (mf i * c)
      rwa [← mul_assoc, ← hc] at this
    have huK : u i ∈ Yk L Y K := mem_Yk.2 ⟨hu i, by
      rw [hc, mul_comm (kf i) (mf i), mul_assoc, mul_comm, ← smul_smul]
      exact L.nsmul_mem (hmf i) _⟩
    rw [piK_sub, piK_shift hY huK hGK.2, sub_self]
  have hpw : piK ρ L X Y K w = 0 := by
    rw [← hsum]
    have : ∀ s : Finset (Fin n), piK ρ L X Y K (∑ i ∈ s, f i • ((g i : {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : V)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        have := piK_smul (ρ := ρ) (L := L) (X := X) (Y := Y) (k := K) (0 : ℂ) (0 : V)
        rwa [zero_smul, zero_smul] at this
      | insert i s his ih =>
        rw [Finset.sum_insert his, piK_add, ih, add_zero, piK_smul, hg i, hzero i, smul_zero]
    exact this Finset.univ
  obtain ⟨c, hc0, hc⟩ := piK_vac hXY hχl hχr hχ0 hLL hdY (k := K) hwX hwY
  rw [hc] at hpw
  exact (smul_eq_zero.1 hpw).resolve_left hc0

end Vac

end Formalism.IndefR.Fin.Four

end
