module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartTies3Site
section
noncomputable section

section
namespace GlobalTheory.Port

open _root_.Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem formsLev_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J' T f bad) (v : HeightOneSpectrum (𝓞 F)) :
    ((S.Uloc v).comap (reGL h _).toMonoidHom ≤ levelVL σ J v (reL h.symm S.Lb)) ∧
    ((T : 𝓞 F) ∉ v.asIdeal → SelfDualAt σ J v (reL h.symm S.Lb)) ∧
    (v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → levelVL σ J v (reL h.symm S.Lb) ≤ (S.Uloc v).comap (reGL h _).toMonoidHom) := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  rw [reL_rfl]
  refine ⟨fun x hx => ?_, fun hT => ?_, fun hb hT x hx => ?_⟩
  · have hx' : reGL rfl _ x ∈ S.Uloc v := hx
    rw [Formalism.L2.Forms.reGL_rfl] at hx'
    exact S.Uloc_lev v hx'
  · exact self_dual_lattice_at F E a σ J' v S.Lb T S.Lb_fin (fun x hx y hy => S.Lb_int y hy x hx) (fun y hy => S.Lb_dual y hy) hT
  · show reGL rfl _ x ∈ S.Uloc v
    rw [Formalism.L2.Forms.reGL_rfl, S.Uloc_hyp v hb hT]
    exact hx

end Gen

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 4000000 in
theorem hypTJC_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T) (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) :
    HypTJC ((Z.loc Fl ht i hi).t β) :=
  hypTJC_of_le ((Z.loc Fl ht i hi).t β)
    (fun w' _ => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').1)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))


set_option maxHeartbeats 4000000 in
theorem hypTJ_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T)
    (hbad : ∀ i hi, ∀ w' ∈ (Z.Fo i hi).bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal)
    (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) : HypTJ ((Z.loc Fl ht i hi).t β) :=
  hypTJ_of_ge ((Z.loc Fl ht i hi).t β)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.2 (fun hb => hbad i hi w' hb h) (T_not_mem hg.1 (hT i hi) w' h))
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))

variable {Tw : TwForms D} {μ : D.what₂.Tup}

end GlobalTheory.Port

end

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
section
noncomputable section

section
namespace GlobalTheory.Port

open _root_.Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ChiDRat (D : D7) : Prop := ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

set_option maxHeartbeats 2000000 in
theorem chRat_ofChiD (h : ChiDRat D) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad} (Y : DetTie S) (c : ℤ)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((DetTw.ofChiD Y c).ch x : ℂˣ) : ℂ) := by
  obtain ⟨r, hr⟩ := h (Y.dt x)
  refine ⟨r ^ c, ?_⟩
  rw [map_zpow₀, hr]
  show _ = (((D.chiD (Y.dt x)) ^ c : ℂˣ) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]

set_option maxHeartbeats 2000000 in
theorem chRat_mem (h : ChiDRat D) {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = (((formsInMem F dt i hi).tw β).ch (((formsInMem F dt i hi).K β).y cl) : ℂ) := by
  by_cases h' : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h']
    intro β cl
    exact chRat_ofChiD h _ _ _
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β cl
    exact chRat_ofChiD h _ _ _

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem fillRec (ex : Extra D L hT Gi Gl Kc Dx cX) : ∀ u w hg, FillTie hT u w hg (Gl.Fl u w hg) := by
  intro u w hg v s b hb
  have h1 := ex.fills_all u w hg v s (b + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : wj D (b + 1) (hT.gat_pos u w hg ⟨v, s⟩) = (((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (show b + 1 - 1 < D.R.m by simpa using hb), D.hcW_e]
    rfl
  rw [h2] at h1
  have e : ((((Gl.Fl u w hg).w v (b + 1) s : ℤ) : ℚ) : ℝ) =
      ((wG D.R ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast, h1]
    unfold wG G.kaJ
    push_cast
    ring
  exact Rat.cast_injective e

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open _root_.Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

section Gen

variable {L : Type} [Field L] [NumberField L]

end Gen

variable {D : D7}

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
section
noncomputable section

section
namespace GlobalTheory.Port

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat Formalism.L2.Ker
open GlobalTheory.TwU (StepCharts ChainCharts AdData AdPins AdTie latCo)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Site

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Tw : TwForms D} {μ : D.what₂.Tup}

def SiteD.inTw (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u μ w hg (Z.lv Fl ht) := Formalism.MainNotions.G.KAat.inTw fun j hj => Z.st Fl ht Gt j hj

def ValAll (Tw : TwForms D) (St : ChainCharts D u μ) : Prop :=
  ∀ i hi, ValuationCompatibleChart (Tw.fm u μ) (St i hi).eY (fun _ => True) (St i hi).chOf (St i hi).K


set_option maxHeartbeats 2000000 in
def foOf (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : ChainCharts D u μ) (hv : ValAll Tw St) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    FormsIn (Tw.fm u μ) (j + 1) hj where
  T := (St (j + 1) hj).T
  bad := (St (j + 1) hj).bad
  eY := (St (j + 1) hj).eY
  okW := fun _ => True
  Ch := (St (j + 1) hj).Ch
  chOf := (St (j + 1) hj).chOf
  lat := (St (j + 1) hj).lat
  K := (St (j + 1) hj).K
  val := by
    unfold ValAll at hv
    exact hv (j + 1) hj
  tw := fun _ => DetTw.ofChiD (detTieOf Hh _) (cTw D (j + 1))

end Site

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure JIn (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  Gd : GroupCompatibilityAll D hT ex.cmp
  Hh : Formalism.L2.Herm.SymmetricHermitianColumns D
  rel : Formalism.L2.Herm.SymmetricRelativeDeterminant D Hh
  St : ChainCharts D u μ
  A : AdData t u μ St
  a : 𝓞 D.host.E
  pins : AdPins A Hh.dt
  tie : AdTie A Hh.dt a
  val : ValAll ex.tw St
  fin : ∀ i hi, Finite (St i hi).Ch
  ord : ∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ, ((St i hi).K β).lev.chi κ ^ n = 1
  base : ∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)
  joint0 : Joint0 Gd.herm.lev0 u (Gd.forms u)
  e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  jointCmpEmbeddingY : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  e0Tw : ∀ φ c y, D.e0Tw u μ φ (e0 c) (jointCmpEmbeddingY y) = φ c y
  lev0 : ∀ β : (St 0 (Nat.zero_le _)).Ch, ((St 0 _).K β).lev.Lb = (Gd.forms u).cls0.lev.Lb ∧
    ((St 0 _).K β).lev.Uloc = (Gd.forms u).cls0.lev.Uloc ∧ ((St 0 _).K β).lev.U = (Gd.forms u).cls0.lev.U ∧
    ∀ (κ : ((St 0 _).K β).lev.U) (κ' : (Gd.forms u).cls0.lev.U), κ.1 = κ'.1 → ((St 0 _).K β).lev.chi κ = (Gd.forms u).cls0.lev.chi κ'
  ch0 : Subsingleton (St 0 (Nat.zero_le _)).Ch
  y0 : ∀ c, ∃ κ : (Gd.forms u).cls0.lev.U, ((St 0 (Nat.zero_le _)).y (e0 c)).1 = ((Gd.forms u).cls0.y c).1 * κ.1 ∧
    (Gd.forms u).cls0.lev.chi κ = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ q ∈ Dx.Qp μ, ((q : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) →
      bc (prV (E := D.host.E) v) κ.1 = 1
  fr0 : ∀ y, (St 0 (Nat.zero_le _)).eY (jointCmpEmbeddingY y) = (Gd.forms u).val0.eY y
  rat : ∀ j, j < D.R.m → (ex.tw.fm u μ).KRat j
  kin : ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y
  chiD : ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

end GlobalTheory.Port
end

end
end

