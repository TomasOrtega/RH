import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.TiedUpDnLoc
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChTwRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST SG ∅ :=
  ⟨(p.deco, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩

/- English proof (translation)
Establish `key` using `PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩`. Introduce and unpack `⟨h, h'⟩`.

Establish `h2` using `key.2 h`. Conclude with `⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩`.
-/
theorem isPtOf_iff (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) :
    IsPtOf hc g p ↔ (g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) ∧
      ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E _ (p.fr P (Pi.single j 1) i) := by
  have key := PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl
  constructor
  · intro h
    exact ⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩
  · rintro ⟨h, h'⟩
    have h2 := key.2 h
    exact ⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩

/- English proof (translation)
Establish `h0` using `TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem adAt_congr_prV (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : prV (E := E) (P.under (𝓞 F)) z = prV (E := E) (P.under (𝓞 F)) z') : adAt F P z = adAt F P z' := by
  have h0 := TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

/- English proof (translation)
Take `⟨⟨-, hd1⟩, -⟩` from `(isPtOf_iff hc g₁ p).1 h₁`. Establish `hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N`. Introduce `P hP`. Rewrite using `[hd1]`. Conclude with `updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)`.

Use `⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _`. Rewrite using `[hloc P.1 P.2]`. Conclude with `p.2 P x`. Use `(isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩ show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)` and prove the remaining obligations.

Rewrite using `[← h₁.fr P i j]`. Apply `adAt_congr_prV` to reduce the goal to its premises. Conclude with `congrArg (fun g => g.1 i j) (hv P.1 P.2)`.
-/
theorem exists_pt_of_agree {g₁ g' : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h₁ : IsPtOf hc g₁ p)
    (hg' : g' ∈ UAd hc n)
    (hv : ∀ P ∈ Q, bc (prV (E := E) (P.under (𝓞 F))) g' = bc (prV (E := E) (P.under (𝓞 F))) g₁) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g' q := by
  obtain ⟨⟨-, hd1⟩, -⟩ := (isPtOf_iff hc g₁ p).1 h₁
  have hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N := by
    intro P hP
    rw [hd1]
    exact updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)
  refine ⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩
  · show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _
    rw [hloc P.1 P.2]
    exact p.2 P x
  · refine (isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩
    show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)
    rw [← h₁.fr P i j]
    apply adAt_congr_prV
    exact congrArg (fun g => g.1 i j) (hv P.1 P.2)

/- English proof (translation)
Take `⟨⟨hgu, hdg⟩, hfg⟩` from `(isPtOf_iff hc g p).1 hg`. Take `⟨⟨hu1, hd1⟩, hf1⟩` from `(isPtOf_iff hc g₁ p).1 hg₁`. Take `⟨⟨hsu, hds⟩, hfs⟩` from `(isPtOf_iff hc (g₁ * s) q).1 hs`. Establish `hsU : s ∈ UAd hc n`. Establish `e : s = g₁⁻¹ * (g₁ * s)` using `by group`.

Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hu1) hsu`. Take `⟨hJ, -⟩` from `mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])`. Establish `hK` using `mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)`. Establish `hc'` using `K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩) (Subgroup.mem_subgroupOf.2 hK)`.

Rewrite `hc'` using `[Subgroup.mem_subgroupOf]`. Establish `e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹)` using `by group`. Establish `hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s)`. Rewrite using `[e]`. Conclude with `decorated_lattice_mul_principal hc n ST SG _ hc'`.

Use `(isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hfg P i l, hf1 P i l]`.
-/
theorem isPtOf_mul {g g₁ s : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q} (h : GLG E n SG)
    (hq : q.deco.1 = p.deco.1.act 1 h) (hg : IsPtOf hc g p) (hg₁ : IsPtOf hc g₁ p) (hs : IsPtOf hc (g₁ * s) q) :
    IsPtOf hc (g * s) q := by
  obtain ⟨⟨hgu, hdg⟩, hfg⟩ := (isPtOf_iff hc g p).1 hg
  obtain ⟨⟨hu1, hd1⟩, hf1⟩ := (isPtOf_iff hc g₁ p).1 hg₁
  obtain ⟨⟨hsu, hds⟩, hfs⟩ := (isPtOf_iff hc (g₁ * s) q).1 hs
  have hsU : s ∈ UAd hc n := by
    have e : s = g₁⁻¹ * (g₁ * s) := by group
    rw [e]
    exact mul_mem (inv_mem hu1) hsu
  obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])
  have hK := mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)
  have hc' := K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩)
    (Subgroup.mem_subgroupOf.2 hK)
  rw [Subgroup.mem_subgroupOf] at hc'
  have e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹) := by group
  have hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s) := by
    rw [e]
    exact decorated_lattice_mul_principal hc n ST SG _ hc'
  refine (isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩
  rw [← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul, hfg P i l, hf1 P i l]

end GlobalTheory.Mem.Col2.ChTwRead

namespace GlobalTheory.Mem.Col2.TC.ChTw

/- English proof (translation)
Introduce `B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU`. Establish `hd : Disjoint (B.primes X).vGs (I.Q a)` using `Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1`. Establish `hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1` using `IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)`. Take `⟨pk, hpk, -⟩` from `hR.k_std (chOf c)`. Establish `hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i)` using `hpk.uni`.

Establish `hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i)`. Establish `e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c))` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)`. Establish `hv : ∀ P ∈ I.Q a, bc (prV (E` using `B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) = bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by`.

Introduce `P hP`. Establish `h1` using `hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩`. Simplify using `only [map_mul, h1, mul_one]`. Take `⟨q, hq⟩` from `ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv`. Take `⟨κ, hκ1, hκq, hκc⟩` from `(hR.lev c x q hq).1 hxU`.

Use `⟨κ, hκ1, hκc, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c)` using `by group`. Establish `hγ : κ.1 = 1`. Establish `h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1`. Rewrite using `[map_one]`.

Conclude with `hκ1`. Conclude with `Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)`. Use `ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq) show ((κ.1, (κ.2.1 : GLG B.fields.E (B.R.N i) (B.primes X).vGs)) • ((I.stp u a i).rep c).1.1.deco).1 = _` and prove the remaining obligations. Rewrite using `[hγ]`. Both sides reduce to the same expression.
-/
theorem locMv_of_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  intro B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hv : ∀ P ∈ I.Q a, bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) =
      bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by
    intro P hP
    have h1 := hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩
    simp only [map_mul, h1, mul_one]
  obtain ⟨q, hq⟩ := ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv
  obtain ⟨κ, hκ1, hκq, hκc⟩ := (hR.lev c x q hq).1 hxU
  refine ⟨κ, hκ1, hκc, fun g hg => ?_⟩
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hγ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  · refine ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq)
    show ((κ.1, (κ.2.1 : GLG B.fields.E (B.R.N i) (B.primes X).vGs)) • ((I.stp u a i).rep c).1.1.deco).1 = _
    rw [hγ]
    rfl
end GlobalTheory.Mem.Col2.TC.ChTw
