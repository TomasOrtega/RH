import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ y D p a hV hp hH1`. Establish `hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1)` using `hH1`. Use `show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0, ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z`. Introduce `z hz'`. Set `instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n)` to `fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i) (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)`.

Set `instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1)` to `Submodule.module _`. Set `instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n)` to `fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i) (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)`. Set `instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1)` to `Submodule.module _`. Set `instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1)` to `Submodule.Quotient.module _`. Take `⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩` from `hR K ι Ω y D p a hV hp`.

Establish `hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, FibreReduction.redCoch y p n w = 0 → ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w'`. Introduce `n w hw h0`. Take `⟨w', h1, h2⟩` from `hker₀ n w hw h0`. Conclude with `⟨w', h1, by convert h2 using 2⟩`. Establish `hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), (p : ℤ) • w = 0 → w = 0` using `fun n w h => hnzd₀ n w (by convert h using 2)`.

Establish `hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), FibreReduction.redCoch y p n ((p : ℤ) • w) = 0` using `fun n w => by convert hkill₀ n w using 3`. Establish `hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ))` using `hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)`. Establish `hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1)`. Conclude with `(hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1`. Establish `dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0` using `fun n w => LinearMap.congr_fun (hsq ℤ K ι _ n) w`.

Establish `dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w` using `fun n w => map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w`. Establish `memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 → w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n` using `fun n w hC hD => Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩`. Set `f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ] KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1` to `LinearMap.lsmul ℤ _ (p : ℤ)`. Establish `hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x)` using `fun x => by`. Rewrite using `[LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]`.

Conclude with `int_smul_eq_zsmul instH (p : ℤ) _`. Establish `hsurj : Function.Surjective f`. Introduce `h`. Proceed by induction on `h using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Establish `hx` using `Submodule.mem_inf.mp x.2`. Establish `hxd : KH.cechD ℤ ι _ 1 x.1 = 0`. Use `hx.2` as an intermediate fact. Rewrite `this` using `[Submodule.restrictScalars_mem, LinearMap.mem_ker]`. Then use the resulting hypothesis. Establish `hrx : FibreReduction.redCoch y p 1 x.1 ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1` using `Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by`.

Rewrite using `[Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩`. Establish `h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ : KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0` using `Subsingleton.elim _ _`. Establish `h0` using `(Submodule.Quotient.mk_eq_zero _).mp h0'`. Take `⟨u, hu, hdu⟩` from `Submodule.mem_map.mp (Submodule.mem_comap.mp h0)`. Take `⟨u', hu', hru'⟩` from `hon 0 u hu`.

Establish `hdu'` using `hdg ℤ K ι _ _ a 0 u' hu'`. Take `⟨x', hx'C, hx'eq⟩` from `hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by`. Rewrite using `[map_sub, hd, hru']`. Conclude with `sub_eq_zero.mpr hdu.symm)`. Establish `hx'Z` using `memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))`.

Use `⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]`. Use `Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]`. Use `show _ = (p : ℤ) • x' - x.1`.

Rewrite using `[← hx'eq]`. Normalize the expressions using the abelian group laws. Establish `hinj : Function.Injective f` using `OrzechProperty.injective_of_surjective_endomorphism f hsurj`. Take `⟨w, hwC, hrw⟩` from `hon 0 z (Submodule.mem_inf.mp hz').1`. Establish `hzd : KH.cechD (ZMod p) ι _ 0 z = 0`.

Use `(Submodule.mem_inf.mp hz').2` as an intermediate fact. Rewrite `this` using `[Submodule.restrictScalars_mem, LinearMap.mem_ker]`. Then use the resulting hypothesis. Take `⟨w', hw'C, hw'eq⟩` from `hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])`. Establish `hw'Z` using `memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))`. Establish `hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]`. Conclude with `Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩`. Take `⟨v, hvC, hdv⟩` from `Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))`. Establish `hv0` using `memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by`.

Rewrite using `[map_sub, dsmul]`. Rewrite `hdv` using `[LinearMap.restrictScalars_apply]`. Rewrite using `[hdv]`. Conclude with `sub_eq_zero.mpr hw'eq)`. Take `⟨s, hs, hsv⟩` from `hZ K ι Ω y a _ hv0`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]`.
-/
theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
