import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitaryStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Take `⟨h, hh, k, hk, e⟩` from `(DoubleCoset.eq Γ K' _ _).1 hij`. Use `hz.1 ((DoubleCoset.eq Γ K _ _).2 ⟨h, hh, b⁻¹ * k * b, (hK k).1 hk, ?_⟩)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `w`. Proceed by induction on `w using Quotient.inductionOn' with`. Consider the case `h x`. Take `⟨i, hi⟩` from `hz.2 (Quotient.mk'' (x * b))`. Take `⟨h, hh, k, hk, e⟩` from `(DoubleCoset.eq Γ K _ _).1 hi`.

Use `⟨i, (DoubleCoset.eq Γ K' _ _).2 ⟨h, hh, b * k * b⁻¹, (hK _).2 ?_, ?_⟩⟩` and prove the remaining obligations. Establish `: b⁻¹ * (b * k * b⁻¹) * b = k` using `by group`. Rewrite using `[this]`. Conclude with `hk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dc_mul_inv_bij {G : Type} [Group G] (Γ K K' : Subgroup G) (b : G) (hK : ∀ x, x ∈ K' ↔ b⁻¹ * x * b ∈ K)
    {ι : Type} (z : ι → G) (hz : Function.Bijective fun i => (Quotient.mk'' (z i) : ClassSet Γ K)) :
    Function.Bijective fun i => (Quotient.mk'' (z i * b⁻¹) : ClassSet Γ K') := by
  constructor
  · intro i j hij
    obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq Γ K' _ _).1 hij
    refine hz.1 ((DoubleCoset.eq Γ K _ _).2 ⟨h, hh, b⁻¹ * k * b, (hK k).1 hk, ?_⟩)
    calc z j = (z j * b⁻¹) * b := by group
      _ = h * z i * (b⁻¹ * k * b) := by rw [e]; group
  · intro w
    induction w using Quotient.inductionOn' with
    | h x =>
      obtain ⟨i, hi⟩ := hz.2 (Quotient.mk'' (x * b))
      obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq Γ K _ _).1 hi
      refine ⟨i, (DoubleCoset.eq Γ K' _ _).2 ⟨h, hh, b * k * b⁻¹, (hK _).2 ?_, ?_⟩⟩
      · have : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [this]
        exact hk
      · calc x = (x * b) * b⁻¹ := by group
          _ = (h * z i * k) * b⁻¹ := by rw [e]
          _ = h * (z i * b⁻¹) * (b * k * b⁻¹) := by group

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨a.1, ?_, a.2⟩` and prove the remaining obligations. Rewrite using `[← qdf_ratHom_stab (hc := hc) H p a, ha, ufGL_ratHom]`. Introduce and unpack `⟨g, hg1, hg2⟩`.

Use `⟨⟨g, hg2⟩, (ratHom_bijective hc n).1 ?_⟩` and prove the remaining obligations. Rewrite using `[qdf_ratHom_stab (hc := hc) H p ⟨g, hg2⟩]`. Conclude with `ufGL_inj hc n (hg1.trans (ufGL_ratHom hc n γ).symm)`.
-/
theorem mem_range_qdStab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
    (H : Subgroup (GLG E n SG)) (p : DecoF E n ST SG Q) (γ : URat hc n) :
    γ ∈ (qdStab (hc := hc) (Θ := Θ) H p).range ↔ ∃ g : UF E n × H × Θ.grp, ufGL E n g.1 = γ.1 ∧ g • p = p := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.1, ?_, a.2⟩
    rw [← qdf_ratHom_stab (hc := hc) H p a, ha, ufGL_ratHom]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨⟨g, hg2⟩, (ratHom_bijective hc n).1 ?_⟩
    rw [qdf_ratHom_stab (hc := hc) H p ⟨g, hg2⟩]
    exact ufGL_inj hc n (hg1.trans (ufGL_ratHom hc n γ).symm)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n _ ST SG Q K _ Hw π T f hB hTπ hST hcard hSG hidx lam Θ q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb cl stab _ lat s y hy hd hs hlat st hinj hr hchr`. Substitute `hJ hb` using the available equality. Set `S` to `stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀`. Establish `hbT' : ∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E` using `E) v) b)).toMonoidHom = S.Uloc v := by`. Introduce `v hv`.

Rewrite using `[S.UlocAlt v hv]`. Conclude with `hbT v ((mem_plUnder_iff_norm hc hST T hTπ v).2 hv)`. Take `⟨S', hLb, hU, hchi⟩` from `GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT' hbO`. Establish `hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1` using `by haveI : Finite (GLG E n SG) := inferInstance`. Use `⟨Nat.card (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)), Nat.card_pos, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, pow_card_eq_one', map_one]`. Take `⟨m, hm, hM⟩` from `stepOfQ_chi_fin hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀ hlam hchr`. Set `e` to `Equiv.ofBijective _ hs`. Set `s' : DecoFCl (K` to `K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → DecoF E n ST SG Q := fun c => s (e.symm c)`. Establish `hs' : ∀ c, (Quotient.mk'' (s' c) : DecoFCl (K` using `K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ) = c := fun c => e.apply_symm_apply c`.

Set `y' : DecoFCl (K` to `K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → UAd hc n := fun c => ⟨y (e.symm c), hy _⟩`. Establish `hy' : ∀ c, FrOver q (y' c).1 (s' c)` using `fun c => hd _`. Set `C` to `recClsFy q (qdf_frLat q) qdf_frExists s' hs' y' hy'`. Establish `hm' : ∀ c a, st c a ∈ URat hc n` using `fun c a => by`. Take `⟨g, hg, -⟩` from `(hr c _).1 ⟨a, rfl⟩`.

Rewrite using `[← hg]`. Conclude with `ufGL_mem hc n _`. Establish `hYU : ∀ c, y c * b⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)` using `fun c => mul_mem (hy c) (inv_mem hbU)`. Use `⟨S', fun c => ⟨y c * b⁻¹, hYU c⟩, fun c => (st c).codRestrict _ (hm' c), ?_, fun c x => ?_, fun c a a' h => hinj c (congrArg Subtype.val h), fun c γ => ?_, hLb, hU, fun x z h => hchi x z h, ?_, fun _ => rfl, fun _ _ => rfl⟩` and prove the remaining obligations. Establish `hC : ∀ c, C.y (e c) = ⟨y c, hy c⟩` using `fun c => Subtype.ext (congrArg y (e.symm_apply_apply c))`.

Establish `hz` using `C.y_bij.comp e.bijective`. Establish `hz' : Function.Bijective fun c => (Quotient.mk'' (⟨y c, hy c⟩ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (Finit …`. Use `hz using 2 with c` and compare the differences between its conclusion and the goal. Simplify using `only [Function.comp_apply, hC]`. Conclude with `dc_mul_inv_bij ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (Fi …`.

Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hU, mem_map_conj]`. Use the proof step `rfl) _ hz'`. Establish `h` using `decoRaw_carries hc n ST SG (hy c) x`. Rewrite `h` using `[← rlc_decoOf_val hc n ST SG (hy c), (hd c).1, ← hlat]`. Use `(h.trans ?_)` and prove the remaining obligations.

Rewrite using `[hLb]`. Use `show _ ↔ ((y c * b⁻¹)⁻¹ : GL (Fin n) _).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]`. Conclude with `(hbL _).symm`. Establish `h` using `C.stabI_range (e c) γ.1 γ.2`.

Express the relevant statement in the definitionally equal form `(⟨γ.1, γ.2⟩ : URat hc n) ∈ (qdStab (hc := hc) (Θ := Θ) (Subgroup.pi Set.univ Hw) (s (e.symm (e c)))).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj (y (e.symm (e c)))).toMonoidHom at h`. Rewrite `h` using `[e.symm_apply_apply, mem_range_qdStab, ← hr]`. Use `Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩, fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩ (h.trans ?_)` and prove the remaining obligations. Rewrite using `[hU, mem_map_conj, mem_map_conj, mem_map_conj]`. Use `show _ ↔ b⁻¹ * ((y c * b⁻¹)⁻¹ * _ * (y c * b⁻¹)) * b ∈ _`.

Establish `e2 : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), b⁻¹ * ((y c * b⁻¹)⁻¹ * g * (y c * b⁻¹)) * b = (y c)⁻¹ * g * y c` using `fun g => by group`. Rewrite using `[e2]`. Conclude with `Iff.rfl`. Use `⟨m, hm, fun κ => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ x, x ∈ S'.U → b⁻¹ * x * b ∈ S.U` using `fun x hx => by`.

Rewrite `hx` using `[hU, mem_map_conj]`. Conclude with `hx`. Establish `hk : b⁻¹ * κ.1 * b ∈ S.U` using `h1 κ.1 κ.2`. Rewrite using `[hchi κ ⟨_, hk⟩ (by show κ.1 = b * (b⁻¹ * κ.1 * b) * b⁻¹; group), hM]`.
-/
theorem chartQ_exists : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Hw π T f hB hTπ hST hcard hSG hidx lam Θ q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb
    cl stab _ lat s y hy hd hs hlat st hinj hr hchr
  subst hJ hb
  classical
  let S := stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀
  have hbT' : ∀ v, (T : 𝓞 F) ∈ v.asIdeal →
      (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v := by
    intro v hv
    rw [S.UlocAlt v hv]
    exact hbT v ((mem_plUnder_iff_norm hc hST T hTπ v).2 hv)
  obtain ⟨S', hLb, hU, hchi⟩ := GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT' hbO
  have hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1 := by
    haveI : Finite (GLG E n SG) := inferInstance
    refine ⟨Nat.card (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)), Nat.card_pos, fun h => ?_⟩
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨m, hm, hM⟩ := stepOfQ_chi_fin hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀ hlam hchr
  let e := Equiv.ofBijective _ hs
  let s' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → DecoF E n ST SG Q := fun c => s (e.symm c)
  have hs' : ∀ c, (Quotient.mk'' (s' c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ) = c :=
    fun c => e.apply_symm_apply c
  let y' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → UAd hc n := fun c => ⟨y (e.symm c), hy _⟩
  have hy' : ∀ c, FrOver q (y' c).1 (s' c) := fun c => hd _
  let C := recClsFy q (qdf_frLat q) qdf_frExists s' hs' y' hy'
  have hm' : ∀ c a, st c a ∈ URat hc n := fun c a => by
    obtain ⟨g, hg, -⟩ := (hr c _).1 ⟨a, rfl⟩
    rw [← hg]
    exact ufGL_mem hc n _
  have hYU : ∀ c, y c * b⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
    fun c => mul_mem (hy c) (inv_mem hbU)
  refine ⟨S', fun c => ⟨y c * b⁻¹, hYU c⟩, fun c => (st c).codRestrict _ (hm' c), ?_, fun c x => ?_,
    fun c a a' h => hinj c (congrArg Subtype.val h), fun c γ => ?_, hLb, hU, fun x z h => hchi x z h, ?_,
    fun _ => rfl, fun _ _ => rfl⟩
  ·
    have hC : ∀ c, C.y (e c) = ⟨y c, hy c⟩ := fun c => Subtype.ext (congrArg y (e.symm_apply_apply c))
    have hz := C.y_bij.comp e.bijective
    have hz' : Function.Bijective fun c => (Quotient.mk'' (⟨y c, hy c⟩ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E)
        (FiniteAdeleRing (𝓞 F) F)) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))) := by
      convert hz using 2 with c
      simp only [Function.comp_apply, hC]
    exact dc_mul_inv_bij ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        (S'.U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) ⟨b, hbU⟩ (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hU, mem_map_conj]
      rfl) _ hz'
  ·
    have h := decoRaw_carries hc n ST SG (hy c) x
    rw [← rlc_decoOf_val hc n ST SG (hy c), (hd c).1, ← hlat] at h
    refine (h.trans ?_)
    rw [hLb]
    show _ ↔ ((y c * b⁻¹)⁻¹ : GL (Fin n) _).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hbL _).symm
  ·
    have h := C.stabI_range (e c) γ.1 γ.2
    change (⟨γ.1, γ.2⟩ : URat hc n) ∈ (qdStab (hc := hc) (Θ := Θ) (Subgroup.pi Set.univ Hw) (s (e.symm (e c)))).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈
        (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj (y (e.symm (e c)))).toMonoidHom at h
    rw [e.symm_apply_apply, mem_range_qdStab, ← hr] at h
    refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩, fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩ (h.trans ?_)
    rw [hU, mem_map_conj, mem_map_conj, mem_map_conj]
    show _ ↔ b⁻¹ * ((y c * b⁻¹)⁻¹ * _ * (y c * b⁻¹)) * b ∈ _
    have e2 : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), b⁻¹ * ((y c * b⁻¹)⁻¹ * g * (y c * b⁻¹)) * b = (y c)⁻¹ * g * y c :=
      fun g => by group
    rw [e2]
    exact Iff.rfl
  ·
    refine ⟨m, hm, fun κ => ?_⟩
    have h1 : ∀ x, x ∈ S'.U → b⁻¹ * x * b ∈ S.U := fun x hx => by
      rw [hU, mem_map_conj] at hx
      exact hx
    have hk : b⁻¹ * κ.1 * b ∈ S.U := h1 κ.1 κ.2
    rw [hchi κ ⟨_, hk⟩ (by show κ.1 = b * (b⁻¹ * κ.1 * b) * b⁻¹; group), hM]

end GlobalTheory.Mem.Col2.ChEx
