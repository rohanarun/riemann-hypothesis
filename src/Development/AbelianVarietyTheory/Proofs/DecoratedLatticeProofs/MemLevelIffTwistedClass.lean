module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479

@[expose] public section

noncomputable section

namespace GlobalTheory.TopVal.TwSet

section Gen

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

theorem lev_set {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E}
    (hJ' : J' = 1) (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (hL : S.Lb = Formalism.L2.Col.stdLat E n) {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n') (ht : 0 < t) (hn : n = r + s * t)
    {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ)
    (hR : ∀ (z : GL (Fin n) (AfE F E)) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))), z ∈ UAd hc n →
      (z ∈ S.U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (parFam h t s P χ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ blockTri (blk2 r)))
    (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H)
    (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hgy : ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) :
    g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, xq⟩ ↔ y ∈ S.U := by
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, xq⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g h2 h1).2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g h2 h1).1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1]

theorem set_univ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ)
    (h1 : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (h2 : ∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P')
    (hR : RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ)
    (z : GL (Fin n) (AfE F E)) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))) (hu : z ∈ UAd hc n) :
    z ∈ S.U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P :=
  (GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary hc hJ { S with chi := 1, chi_triv := fun _ _ => rfl } (fun w => ⟨(Λ w).H, 1⟩) emb HQ (fun _ => 1) h1 h2
    (Filter.Eventually.of_forall fun _ _ _ => rfl)
    (fun x hx hs hv => ⟨(hR x hx hs hv).1, fun _ _ _ => by simp⟩) z (Set.mem_univ z) hz hu).1

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem under_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))


set_option maxHeartbeats 2000000 in
theorem mem_levS_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st} (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (Lev.EAf (I.rec7 l Z))) (hβ : β = 1)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (hPg : Pg = (B.primes X).vGs) (hQ : Q = I.Q a)
    (P' : LevelP Pg B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ PP (h : PP ∈ (B.primes X).vGs) (h' : PP ∈ Pg), g ⟨PP, h'⟩ ∈ (I.Ps ⟨PP, h⟩).H)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank) (g : Formalism.L2.Theta.GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    g ∈ levS _ β (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr Pg Q P' cg ξ Lev.Frm.B) ↔
      ∃ κ : S.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  subst hβ hPg hQ
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  let c : (I.stX a).Cl := ⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩
  have hR0 := GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c
    (fun PP => (Units.map B.embLL.toMonoidHom).comp
      (Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP)) (fun _ _ _ => rfl)
  have hR := set_univ (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (under_inj I hOk a) hR0
  have key := @lev_set B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) hR
    P' cg (fun PP => (ξ PP)⁻¹) (fun x => (hH x).trans ⟨fun h w => h w.1 w.2 w.2, fun h PP h1 _ => h ⟨PP, h1⟩⟩)
  refine ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).2 κ.2⟩⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' g)
  exact ⟨⟨y, (key _ y hy).1 hh.2⟩, hh.1, hy⟩

end Gen

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Args

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 1000000 in
theorem lev_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (g : G0 a.x.R.Pg (w.st Z).toD7.R.r) :
    g ∈ (a.x.R.toRealDat.levR a.x.F.lv2 true).H ↔
      ∀ PP (h : PP ∈ (B.primes w.px).vGs) (h' : PP ∈ a.x.R.Pg), g ⟨PP, h'⟩ ∈ (TC.Ps w.I ⟨PP, h⟩).H := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have key : ∀ g : G0 t.r.z.R.Pg (w.st Z).toD7.R.r, t.r.z.R.eG.symm g ∈ lev1 w.I ↔
      ∀ PP (h : PP ∈ (B.primes w.px).vGs) (h' : PP ∈ t.r.z.R.Pg), g ⟨PP, h'⟩ ∈ (TC.Ps w.I ⟨PP, h⟩).H := by
    intro g
    have e := fun PP h h' => t.r.z.idG (t.r.z.R.eG.symm g) PP h h'
    simp only [MulEquiv.apply_symm_apply] at e
    refine ⟨fun hg PP h h' => ?_, fun hg PP _ => ?_⟩
    · rw [e PP h h']
      exact hg ⟨PP, h⟩ (Set.mem_univ _)
    · have h' : PP.1 ∈ t.r.z.R.Pg := by
        have := t.r.z.lev.Pg
        exact (congrArg (PP.1 ∈ ·) this).mpr PP.2
      have := hg PP.1 PP.2 h'
      rw [e PP.1 PP.2 h'] at this
      exact this
  run_tac Lean.Elab.Tactic.withMainContext do
    let e ← Lean.Elab.Term.elabTerm (← `($(Lean.mkIdent `key) $(Lean.mkIdent `g))) none
    (← Lean.Elab.Tactic.getMainGoal).assign e
    Lean.Elab.Tactic.replaceMainGoal []

end Args



end GlobalTheory.TopVal.TwSet

end
