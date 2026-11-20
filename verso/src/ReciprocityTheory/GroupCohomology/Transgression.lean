import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.Section
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.TransgressionB

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function InflationRestrictionInvariants InflationTransgression

universe u

/- English proof (translation)
Introduce `R _ G _ _ _ _ _ _ M _ N _ hNc Q P hP I hI`. Establish `hE : ∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy, M.coch.d 1 y = P.hom.f 2 z ∧ x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy`. Introduce `x`. Take `⟨f0, hf, hx⟩` from `exists_cls x.1`. Establish `hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m` using `fun s => (conj_fix_iff M N s f0 hf).1 (by`.

Rewrite using `[← hx]`. Conclude with `(hI x.1).1 x.2 s (conjN M N s) (fun g => rfl) (fun m => rfl))`. Take `⟨y, z, hz, hd, hres⟩` from `exists_lift M N Q P hP hNc f0 hf hinv`. Conclude with `⟨y, z, hz, by rw [hres]; exact hf, hd, by rw [hx]; exact cls_congr _ _ hres.symm⟩`. Use `choose yf zf hzf hyf hdf hxf using hE`.

Establish `key : ∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I), M.coch.d 1 y = P.hom.f 2 z → x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy → Q.coch.cls 2 (zf x) (hzf x) = Q.coch.cls 2 z hz`. Introduce `y z hz hy x hd hx`. Apply `cls_unique M N Q P hP _ _ _ _ _ _ (hdf x) hd` to reduce the goal to its premises. Rewrite using `[map_sub, ← cls_eq_iff (hyf x) hy, ← hxf x, ← hx]`. Set `T : I → Q.H 2` to `fun x => Q.coch.cls 2 (zf x) (hzf x)`.

Establish `hadd : ∀ x x' : I, T (x + x') = T x + T x'` using `fun x x' => by`. Establish `hy : (M.resSub N).coch.d 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x + yf x')) = 0`. Rewrite using `[map_add]`. Conclude with `d_add_eq_zero (hyf x) (hyf x')`. Use `(key (yf x + yf x') (zf x + zf x') (d_add_eq_zero (hzf x) (hzf x')) hy (x + x') (by rw [map_add, map_add, hdf, hdf]) ?_).trans rfl` and prove the remaining obligations.

Rewrite using `[Submodule.coe_add, hxf x, hxf x', cls_add]`. Conclude with `cls_congr _ _ (map_add _ _ _).symm`. Establish `hsmul : ∀ (r : R) (x : I), T (r • x) = r • T x` using `fun r x => by`. Establish `hy : (M.resSub N).coch.d 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (r • yf x)) = 0`. Rewrite using `[map_smul]`.

Conclude with `d_smul_eq_zero r (hyf x)`. Use `(key (r • yf x) (r • zf x) (d_smul_eq_zero r (hzf x)) hy (r • x) (by rw [map_smul, map_smul, hdf]) ?_).trans rfl` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, hxf x, cls_smul]`. Conclude with `cls_congr _ _ (map_smul _ _ _).symm`. Set `tg : I →ₗ[R] Q.H 2` to `{ toFun := T, map_add' := hadd, map_smul' := hsmul }`.

Use `⟨tg, fun y z hz hy x hd hx => key y z hz hy x hd hx, fun x => ⟨yf x, zf x, hzf x, hyf x, hdf x, hxf x⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Express the relevant statement in the definitionally equal form `Q.coch.cls 2 (zf x) (hzf x) = 0 at h0`.

Rewrite `h0` using `[cls_eq_zero_iff]`. Take `⟨v, hv⟩` from `mem_B_succ.1 h0`. Establish `hd' : M.coch.d 1 (yf x - P.hom.f 1 v) = 0`. Rewrite using `[map_sub, hdf, ← P.hom.comm, hv, sub_self]`. Use `⟨M.coch.cls 1 _ hd', ?_⟩` and prove the remaining obligations.

Rewrite using `[Hom.H_cls, hxf x]`. Apply `cls_congr` to reduce the goal to its premises. Establish `hc : (M.resSub N).coch.d 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)) = 0`. Establish `e : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) = (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x) - (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x - P.hom.f 1 v)`. Rewrite using `[map_sub, sub_sub_cancel]`.

Rewrite using `[e]`. Conclude with `d_sub_eq_zero (hyf x) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hd')`. Establish `h1` using `cocycle_one (M.resSub N) _ hc`. Establish `hconst : ∀ g : Fin 1 → N, ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 g = ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 (e1 1)` using `fun g => by show P.u (v.1 fun i => P.φ (g i : G)) = P.u (v.1 fun _ => P.φ ((1 : N) : G))`. Establish `e : ∀ i, P.φ (g i : G) = 1` using `fun i => by`.

Rewrite using `[phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]`. Simplify using `only [e, OneMemClass.coe_one, map_one]`. Establish `h0' : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) = 0` using `Subtype.ext (funext fun g => by rw [hconst, h1]; rfl)`. Rewrite using `[map_sub, h0', sub_zero]`. Introduce and unpack `⟨c, hc⟩`.

Take `⟨c0, hc0, rfl⟩` from `exists_cls c`. Express the relevant statement in the definitionally equal form `Q.coch.cls 2 (zf x) (hzf x) = 0`. Rewrite using `[key c0 0 (map_zero _) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hc0) x (by rw [hc0, map_zero]) (by rw [← hc, Hom.H_cls])]`. Both sides reduce to the same expression. Introduce `w`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Take `⟨z, hz, rfl⟩` from `exists_cls w`. Rewrite `hw` using `[Hom.H_cls, cls_eq_zero_iff]`. Take `⟨y, hy⟩` from `mem_B_succ.1 hw`.

Set `q : Q.V` to `z.1 ![1, 1]`. Set `vq : Q.coch.X 1` to `⟨fun _ => q, continuous_const⟩`. Take `⟨z', hz'e⟩ : ∃ z', z' = z - Q.coch.d 1 vq` from `⟨_, rfl⟩`. Take `⟨y', hy'e⟩ : ∃ y', y' = y - P.hom.f 1 vq` from `⟨_, rfl⟩`. Establish `hz'c : Q.coch.d 2 z' = 0` using `by rw [hz'e, map_sub, hz, Q.coch.dd, sub_zero]`.

Establish `hd' : M.coch.d 1 y' = P.hom.f 2 z'`. Rewrite using `[hy'e, hz'e, map_sub, map_sub, hy, P.hom.comm]`. Establish `hz'1 : z'.1 ![1, 1] = 0`. Rewrite using `[hz'e]`. Use `show z.1 ![1, 1] - (Q.coch.d 1 vq).1 ![1, 1] = 0`.

Rewrite using `[oneDifferential_val]`. Use `show q - (Q.rho 1 q - q + q) = 0`. Simplify using the standard rewrite rules. Establish `hres : (M.resSub N).coch.d 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y') = 0`. Rewrite using `[← (Pair.res M N.subtype continuous_subtype_val).hom.comm 1 y', hd']`.

Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Use `show P.u (z'.1 fun i => P.φ (g i : G)) = 0`. Establish `e : (fun i => P.φ (g i : G)) = ![1, 1]` using `funext fun i => by`. Rewrite using `[phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]`. Apply the tactic sequence `fin_cases i <;> rfl`.

Rewrite using `[e, hz'1, map_zero]`. Establish `hy'1 : (fun g => y'.1 (e1 g)) 1 = 0` using `cocycle_one (M.resSub N) _ hres`. Establish `hID` using `inflD_of_d M N Q P hP y' z' hd'`. Establish `hmem : (M.resSub N).coch.cls 1 _ hres ∈ I`. Rewrite using `[hI]`.

Introduce `s c hφ hu`. Conclude with `pair_fix M N s c hφ hu _ hres (y'.1 (e1 s)) (fun n => inflD_conj M N _ hy'1 hID s n)`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Use `show Q.coch.cls 2 (zf _) (hzf _) = Q.coch.cls 2 z hz`. Rewrite using `[key y' z' hz'c hres ⟨_, hmem⟩ hd' rfl, cls_eq_iff]`.

Conclude with `⟨-vq, by rw [hz'e, map_neg]; abel⟩`. Introduce and unpack `⟨x, rfl⟩ show P.hom.H 2 (Q.coch.cls 2 (zf x) (hzf x)) = 0`. Rewrite using `[Hom.H_cls, cls_eq_zero_iff]`. Conclude with `⟨yf x, hdf x⟩`.
-/
theorem transgression_holds : TransgressionStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hNc Q P hP I hI
  have hE : ∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy,
      M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy := by
    intro x
    obtain ⟨f0, hf, hx⟩ := exists_cls x.1
    have hinv : ∀ s : G, ∃ m : M.V, ∀ n : N,
        M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := fun s =>
      (conj_fix_iff M N s f0 hf).1 (by
        rw [← hx]; exact (hI x.1).1 x.2 s (conjN M N s) (fun g => rfl) (fun m => rfl))
    obtain ⟨y, z, hz, hd, hres⟩ := exists_lift M N Q P hP hNc f0 hf hinv
    exact ⟨y, z, hz, by rw [hres]; exact hf, hd, by rw [hx]; exact cls_congr _ _ hres.symm⟩
  choose yf zf hzf hyf hdf hxf using hE
  have key : ∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I),
      M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      Q.coch.cls 2 (zf x) (hzf x) = Q.coch.cls 2 z hz := by
    intro y z hz hy x hd hx
    apply cls_unique M N Q P hP _ _ _ _ _ _ (hdf x) hd
    rw [map_sub, ← cls_eq_iff (hyf x) hy, ← hxf x, ← hx]
  let T : I → Q.H 2 := fun x => Q.coch.cls 2 (zf x) (hzf x)
  have hadd : ∀ x x' : I, T (x + x') = T x + T x' := fun x x' => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x + yf x')) = 0 := by
      rw [map_add]; exact d_add_eq_zero (hyf x) (hyf x')
    refine (key (yf x + yf x') (zf x + zf x') (d_add_eq_zero (hzf x) (hzf x')) hy (x + x')
      (by rw [map_add, map_add, hdf, hdf]) ?_).trans rfl
    rw [Submodule.coe_add, hxf x, hxf x', cls_add]
    exact cls_congr _ _ (map_add _ _ _).symm
  have hsmul : ∀ (r : R) (x : I), T (r • x) = r • T x := fun r x => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (r • yf x)) = 0 := by
      rw [map_smul]; exact d_smul_eq_zero r (hyf x)
    refine (key (r • yf x) (r • zf x) (d_smul_eq_zero r (hzf x)) hy (r • x)
      (by rw [map_smul, map_smul, hdf]) ?_).trans rfl
    rw [Submodule.coe_smul, hxf x, cls_smul]
    exact cls_congr _ _ (map_smul _ _ _).symm
  let tg : I →ₗ[R] Q.H 2 := { toFun := T, map_add' := hadd, map_smul' := hsmul }
  refine ⟨tg, fun y z hz hy x hd hx => key y z hz hy x hd hx,
    fun x => ⟨yf x, zf x, hzf x, hyf x, hdf x, hxf x⟩, ?_, ?_⟩
  · intro x
    constructor
    · intro h0
      change Q.coch.cls 2 (zf x) (hzf x) = 0 at h0
      rw [cls_eq_zero_iff] at h0
      obtain ⟨v, hv⟩ := mem_B_succ.1 h0
      have hd' : M.coch.d 1 (yf x - P.hom.f 1 v) = 0 := by
        rw [map_sub, hdf, ← P.hom.comm, hv, sub_self]
      refine ⟨M.coch.cls 1 _ hd', ?_⟩
      rw [Hom.H_cls, hxf x]
      apply cls_congr
      have hc : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)) = 0 := by
        have e : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) =
            (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x) -
              (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x - P.hom.f 1 v) := by
          rw [map_sub, sub_sub_cancel]
        rw [e]
        exact d_sub_eq_zero (hyf x) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hd')
      have h1 := cocycle_one (M.resSub N) _ hc
      have hconst : ∀ g : Fin 1 → N,
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 g =
            ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 (e1 1) := fun g => by
        show P.u (v.1 fun i => P.φ (g i : G)) = P.u (v.1 fun _ => P.φ ((1 : N) : G))
        have e : ∀ i, P.φ (g i : G) = 1 := fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
        simp only [e, OneMemClass.coe_one, map_one]
      have h0' : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) = 0 :=
        Subtype.ext (funext fun g => by rw [hconst, h1]; rfl)
      rw [map_sub, h0', sub_zero]
    · rintro ⟨c, hc⟩
      obtain ⟨c0, hc0, rfl⟩ := exists_cls c
      change Q.coch.cls 2 (zf x) (hzf x) = 0
      rw [key c0 0 (map_zero _) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hc0) x
        (by rw [hc0, map_zero]) (by rw [← hc, Hom.H_cls])]
      rfl
  · intro w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := exists_cls w
      rw [Hom.H_cls, cls_eq_zero_iff] at hw
      obtain ⟨y, hy⟩ := mem_B_succ.1 hw
      let q : Q.V := z.1 ![1, 1]
      let vq : Q.coch.X 1 := ⟨fun _ => q, continuous_const⟩
      obtain ⟨z', hz'e⟩ : ∃ z', z' = z - Q.coch.d 1 vq := ⟨_, rfl⟩
      obtain ⟨y', hy'e⟩ : ∃ y', y' = y - P.hom.f 1 vq := ⟨_, rfl⟩
      have hz'c : Q.coch.d 2 z' = 0 := by rw [hz'e, map_sub, hz, Q.coch.dd, sub_zero]
      have hd' : M.coch.d 1 y' = P.hom.f 2 z' := by
        rw [hy'e, hz'e, map_sub, map_sub, hy, P.hom.comm]
      have hz'1 : z'.1 ![1, 1] = 0 := by
        rw [hz'e]
        show z.1 ![1, 1] - (Q.coch.d 1 vq).1 ![1, 1] = 0
        rw [oneDifferential_val]
        show q - (Q.rho 1 q - q + q) = 0
        simp
      have hres : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y') = 0 := by
        rw [← (Pair.res M N.subtype continuous_subtype_val).hom.comm 1 y', hd']
        refine Subtype.ext (funext fun g => ?_)
        show P.u (z'.1 fun i => P.φ (g i : G)) = 0
        have e : (fun i => P.φ (g i : G)) = ![1, 1] := funext fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
          fin_cases i <;> rfl
        rw [e, hz'1, map_zero]
      have hy'1 : (fun g => y'.1 (e1 g)) 1 = 0 := cocycle_one (M.resSub N) _ hres
      have hID := inflD_of_d M N Q P hP y' z' hd'
      have hmem : (M.resSub N).coch.cls 1 _ hres ∈ I := by
        rw [hI]
        intro s c hφ hu
        exact pair_fix M N s c hφ hu _ hres (y'.1 (e1 s)) (fun n => inflD_conj M N _ hy'1 hID s n)
      refine ⟨⟨_, hmem⟩, ?_⟩
      show Q.coch.cls 2 (zf _) (hzf _) = Q.coch.cls 2 z hz
      rw [key y' z' hz'c hres ⟨_, hmem⟩ hd' rfl, cls_eq_iff]
      exact ⟨-vq, by rw [hz'e, map_neg]; abel⟩
    · rintro ⟨x, rfl⟩
      show P.hom.H 2 (Q.coch.cls 2 (zf x) (hzf x)) = 0
      rw [Hom.H_cls, cls_eq_zero_iff]
      exact ⟨yf x, hdf x⟩

end ReciprocityTheory.Coh
