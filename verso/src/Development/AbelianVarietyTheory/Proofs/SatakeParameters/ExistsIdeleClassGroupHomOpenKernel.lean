import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.IdeleClass

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Use `show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x`. Use `Pi.mulSingle_eq_same v (x : v.adicCompletion E)` and compare the differences between its conclusion and the goal.
-/
theorem localIdele_snd_self' (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

/- English proof (translation)
Use `show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1`. Use `Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)` and compare the differences between its conclusion and the goal.
-/
theorem localIdele_snd_ne' (v w : HeightOneSpectrum (𝓞 E)) (h : w ≠ v) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem classHom_val (a : Ideles E) :
    ((((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finIdele_apply (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.Mem.UnitIndex.finIdele E a : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v =
      (a : AdeleRing (𝓞 E) E).2 v := rfl

/- English proof (translation)
Establish `h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1`. Rewrite using `[← GlobalTheory.Idele.smul_one_eq]`. Conclude with `(GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v`. Establish `hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1` using `Units.ext (by rw [classHom_val, h]; rfl)`. Use `show ClassGroup.mk E _ = 1`.

Rewrite using `[hu, map_one]`.
-/
theorem classHom_eq_one_of_mem_unitIdl {a : Ideles E} (ha : a ∈ GlobalTheory.Mem.Chr.unitIdl E) :
    GlobalTheory.Mem.UnitIndex.classHom E a = 1 := by
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq]
    exact (GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1 :=
    Units.ext (by rw [classHom_val, h]; rfl)
  show ClassGroup.mk E _ = 1
  rw [hu, map_one]

/- English proof (translation)
Introduce `_ ha` and use `classHom_eq_one_of_mem_unitIdl E ha`.
-/
theorem unitIdl_le_ker : GlobalTheory.Mem.Chr.unitIdl E ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker :=
  fun _ ha => classHom_eq_one_of_mem_unitIdl E ha

/- English proof (translation)
Introduce and unpack `_ ⟨y, -, rfl⟩ v`. Use `show Valued.v (1 : v.adicCompletion E) = 1`. Conclude with `map_one _`.
-/
theorem infConn_le_unitIdl : infConn E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  rintro _ ⟨y, -, rfl⟩ v
  show Valued.v (1 : v.adicCompletion E) = 1
  exact map_one _

/- English proof (translation)
Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) = FiniteAdeleRing.unitEmbedding (𝓞 E) E k` using `Units.ext rfl`. Use `show ClassGroup.mk E _ = 1`. Rewrite using `[ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding, FractionalIdeal.coe_spanSingleton]`. Conclude with `⟨⟨(k : E), rfl⟩⟩`.
-/
theorem diagUnits_range_le_ker : (diagUnits E).range ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker := by
  rintro _ ⟨k, rfl⟩
  have hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) =
      FiniteAdeleRing.unitEmbedding (𝓞 E) E k := Units.ext rfl
  show ClassGroup.mk E _ = 1
  rw [ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(k : E), rfl⟩⟩

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[localIdele_snd_self']`. Conclude with `hx`.

Rewrite using `[localIdele_snd_ne' E v w hw]`. Conclude with `map_one _`.
-/
theorem localIdele_mem_unitIdl (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self']
    exact hx
  · rw [localIdele_snd_ne' E v w hw]
    exact map_one _

open Classical in
/- English proof (translation)
Rewrite using `[GlobalTheory.Idele.ord_vw, finIdele_apply]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[localIdele_snd_self', if_pos rfl]`. Establish `hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1)` using `hx`.

Rewrite using `[hx', WithZero.log_exp]`. Both sides reduce to the same expression. Rewrite using `[localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]`. Both sides reduce to the same expression.
-/
theorem ord_vw_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) w =
      if v = w then 1 else 0 := by
  rw [GlobalTheory.Idele.ord_vw, finIdele_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self', if_pos rfl]
    have hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1) := hx
    rw [hx', WithZero.log_exp]
    rfl
  · rw [localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]
    rfl

/- English proof (translation)
Establish `hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0` using `by simpa using v.ne_bot`. Establish `h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) = (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)`. Use `GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w, FractionalIdeal.count_maximal]`. Establish `hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits (localIdele E v x) = FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩` using `Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])`.

Use `show ClassGroup.mk E _ = _`. Rewrite using `[hu, ClassGroup.mk_mk0]`.
-/
theorem classHom_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) :
    GlobalTheory.Mem.UnitIndex.classHom E (localIdele E v x) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  classical
  have hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by simpa using v.ne_bot
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) =
      (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) := by
    refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_
    rw [GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w,
      FractionalIdeal.count_maximal]
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits
      (localIdele E v x) =
      FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
    Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])
  show ClassGroup.mk E _ = _
  rw [hu, ClassGroup.mk_mk0]

end GlobalTheory.IdeleClass

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _`. Use `⟨GlobalTheory.Mem.UnitIndex.classHom E, Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl, sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E) ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleCla …` and prove the remaining obligations.
-/
theorem exists_ideleClassHom : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro E _ _
  refine ⟨GlobalTheory.Mem.UnitIndex.classHom E,
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl,
    sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)),
    fun v x hx => GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E
      (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hx),
    fun v x hx => GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hx⟩

end GlobalTheory
