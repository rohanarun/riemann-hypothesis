module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.JSpanPf

private theorem span_of_bc {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
    {S : Formalism.L2.Col.GSD K} {S' : Formalism.L2.Col.GSD L} (b : Formalism.L2.Col.GSDBC ι S S') {M M' : Type} [AddCommGroup M'] [Module L M']
    (r : S.EqFun → M) (r' : S'.EqFun ≃ₗ[L] M') (c : L →+* ℂ) {α α' U U' : Type} (n : NormedAddCommGroup U)
    (n' : NormedAddCommGroup U') (ip : InnerProductSpace ℂ U) (ip' : InnerProductSpace ℂ U') (hα : α' = α) (hU : U' = U)
    (hn : HEq n' n) (hip : HEq ip' ip) (j : M → α → U) (j' : M' →ₛₗ[c] (α' → U'))
    (h : ∀ φ, HEq (j' (r' (b.lift φ))) (j (r φ))) (x' : M') :
    ∃ (m : ℕ) (a : Fin m → L) (x : Fin m → M), HEq (j' x') (∑ k, c (a k) • j (x k)) := by
  subst hα hU
  cases hn
  cases hip
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  obtain ⟨φ', rfl⟩ := r'.surjective x'
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (b.mem_span_lift F φ')
  choose ψ hψ using fun k => (g k).2
  refine ⟨m, a, fun k => r (ψ k), heq_of_eq ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.map_smulₛₗ, ← hψ k, eq_of_heq (h (ψ k))]


set_option maxHeartbeats 4000000 in
private theorem exists_bc {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hE : Enl0 B B') (hf : HEq f' f) (hpx : HEq w'.px w.px)
    (k k' : ℕ) (hk : k' = k) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) :
    ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k)
      (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 k'),
      ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k).EqFun) d d', HEq d' d →
        HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((b.lift ψ).1 d').1)
          (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hk
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine GlobalTheory.Mem.R3.DefLatBC.gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm


set_option maxHeartbeats 2000000 in
private theorem gf_eq {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m)
    (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) : Type) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at h
  subst h
  have e0 : i = i' := Fin.ext hi
  subst e0
  rfl

end GlobalTheory.Mem.R3.Rw.JSpanPf

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → RSideW z Wt' R' → JSpan z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hRS i i' hii x'
  obtain ⟨ι, hι⟩ := exists_iota_comp B.embLL B'.embLL hE.2.2.2
  obtain ⟨b, hb⟩ := GlobalTheory.Mem.R3.Rw.JSpanPf.exists_bc w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) ι hι
  have hj := fun φ => hRS.2.2.2.2.2.2.2.2.2.2.2.2.2 i i' hii (Formalism.L2.Col.mtKOk _ _ _ _ hX _) (Formalism.L2.Col.mtKOk _ _ _ _ hX' _) φ
    (b.lift φ) (hb φ)
  have hc := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have key := GlobalTheory.Mem.R3.Rw.JSpanPf.span_of_bc b
    (fun φ => (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX _) φ)
    ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX' _))
    B'.embLL (z.R.cV i).nW (R'.cV i').nW (z.R.cV i).iW (R'.cV i').iW (GlobalTheory.Mem.R3.Rw.JSpanPf.gf_eq Z Z' hE.1 i i' hii)
    (eq_of_heq hc.1) hc.2.2.1 hc.2.2.2.1
    (fun x => z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :))))
    ((by with_unfolding_all exact (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) :))) ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (x' :)))
  exact (by with_unfolding_all exact (key :))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsAtOfPlUnder
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder)

theorem readsAt_of_plUnder (X X' : Stages) (h : Enl X.B X'.B) (hc : Carried X.toD7 X'.toD7) (v' : X'.B.places.Pl)
    (i : X.toD7.ntw.Tw) (i' : X'.toD7.ntw.Tw) (b : Bool) (hi : HEq i i')
    (hr : ReadsAt (D := X.toD7) i b (plUnder h v')) : ReadsAt (D := X'.toD7) i' b v' := by
  intro x'

  have hx : X'.B.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) ∈ X'.B.embLL '' (X'.B.LL0 : Set X'.B.LL) :=
    ⟨_, (x' : ↥X'.toD7.LL0).2, rfl⟩
  rw [h.2.2.1] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have hint' : IsIntegral ℤ (X.B.embLL y) := by
    rw [hye]
    exact (RingOfIntegers.isIntegral_coe x').map
      ((X'.toD7.what₂.embLL.comp (algebraMap ↥X'.toD7.LL0 X'.toD7.what₂.LL)).toIntAlgHom)
  have hint : IsIntegral ℤ (⟨y, hy⟩ : ↥X.toD7.LL0) := by
    refine (isIntegral_algHom_iff ((X.toD7.what₂.embLL.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL)).toIntAlgHom) ?_).1 (by exact hint')
    exact X.toD7.what₂.embLL.injective.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL).injective
  let x : 𝓞 ↥X.toD7.LL0 := ⟨⟨y, hy⟩, hint⟩
  have e : X.toD7.what₂.embLL ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) =
      X'.toD7.what₂.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := hye

  obtain ⟨h1, h2⟩ := hc.emb i i' hi x x' e
  have hside : HEq (sideEmb i b (x : ↥X.toD7.LL0)) (sideEmb i' b (x' : ↥X'.toD7.LL0)) := by
    cases b
    · simpa [sideEmb] using h2
    · simpa [sideEmb] using h1
  have hleft := ((same_basic hc.exp.gal hc.exp.set hc.exp.frm).2.2.2.2 i i' hi).2.2 _ _ hside

  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := by
    apply RingOfIntegers.ext
    apply X'.B.embLL.injective
    exact (embLL_incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL)).trans e
  have hright : 0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
    refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
      (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
    have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
    rw [hmap] at hm
    exact hm
  exact hleft.symm.trans ((hr x).trans hright)

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
section
noncomputable section

namespace GlobalTheory.LevCmp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (κ : GAf L n) (c : ℂ) : Prop := ∀ g, F (g * κ) = c • F g

def FrameAut (θ : GAf L n ≃* GAf L n) : Prop :=
  (∀ κ, θ κ ∈ Umax L n ↔ κ ∈ Umax L n) ∧ ∀ v κ, TrivOutside {v} (θ κ) ↔ TrivOutside {v} κ

def cx {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) : J →* ℂˣ := (Units.map e.toMonoidHom).comp χ

theorem cx_apply {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) :
    ((cx e χ κ : ℂˣ) : ℂ) = e (χ κ : Kˣ) := rfl

def LevEq (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (J' : Subgroup (GAf L n)) (χ' : J' →* ℂˣ) : Prop :=
  J = J' ∧ ∀ κ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩

def WtMatch {K : Type} [Field K] (e : K →+* ℂ) {W W' : Type} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W'),
    ∀ γ, LinearMap.toMatrix b' b' (ρ' γ) = (LinearMap.toMatrix b b (ρ γ)).map e

end Gen

variable {D : D7}

def SideRead (i : D.ntw.Tw) (b : Bool) (k : ℕ) (e : NX.Kk D i k →+* ℂ) : Prop :=
  ∀ x : ↥D.LL0, e (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x)) = embLL0 D x

def ReadsHecke {i : D.ntw.Tw} {k : ℕ} (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E) : Prop :=
  ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofOk D i k)).toMonoidHom).comp ψ) χ


variable (D) in
def GalOf (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) ∧ ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀) χ


variable (D) in
def GPlaces : Prop :=
  (∀ k v, D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) ∧ ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v) ∧
    (∀ u ∈ gPl D, ∃ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.v = u ∧ s.w = D.naut.plGw k v) ∧
    ∃ k, Nonempty (D.nd.PlG k)


variable (D) in
def ParaShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) : Prop :=
  ∀ v ∈ qPl D η, ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
    NG.IsCompAt η s ξ ∧ NG.LevelPara J χ s D.R.r ξ


variable (D) in
def GrpShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) : Prop :=
  NG.IsProdLevel J ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s D.R.r (s.loc _ κ))) ∧
    (∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s D.R.r (s.loc _ κ))) ∧
    ∀ κ, TrivOutside (gPl D ∪ qPl D η)ᶜ κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)

abbrev cell (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) :=
  X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA

abbrev eta (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (v : D.what₂.places.Pl) (j : Fin D.R.m) : HChar D.host.E :=
  cf.mu0 j * xi (D.what₂.muTw v)

abbrev mtAt (M : MtFam D) (v : D.what₂.places.Pl) (j : Fin D.R.m) : MtReal D (D.what₂.muTw v) (j.1 + 1) :=
  M (D.what₂.muTw v) (j.1 + 1) (by omega) (by omega)

def CellWt {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) : Prop := WtMatch e (cell X b hA j).ρ m.wt.ρ

def Joint (η : HChar D.host.E) {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) : Prop :=
  ∃ (θ : GAf D.host.E D.R.nV ≃* GAf D.host.E D.R.nV) (J₁ : Subgroup (GAf D.host.E D.R.nV)) (e : NX.Kk D i k →+* ℂ)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ω : (cell X b hA j).W →ₛₗ[e] V),
    FrameAut θ ∧ SideRead i b k e ∧ Function.Injective ω ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    (∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v →
      ∀ κ, TrivOutside {s.v} κ → NG.UniRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    ∀ κ ∈ J₁, ∃ c c' : ℂ, (∀ x, Eig (m.real x) (θ κ) c) ∧ (∀ f, Eig (fun g => ω (((cell X b hA j).real f).1 g)) (θ κ) c') ∧
      ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → TrivOutside {s.v} κ →
        c ^ (D.host.g kk - 1) = c' ^ (D.host.g kk - 1)

end GlobalTheory.LevCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

def twL {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (Dof x) A) : GlobalTheory.ExportSeries.Twist (DL x L) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def twB {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (DL x L) A) : GlobalTheory.ExportSeries.Twist (Dof x) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def frL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (F : GlobalTheory.ExportSeries.Frame S U) : @GlobalTheory.ExportSeries.Frame (DL x L) ((S)) ((U)) where
  ψ := (by with_unfolding_all exact (F.ψ :))
  θ := (by with_unfolding_all exact (F.θ :))
  sT := (by with_unfolding_all exact (F.sT :))
  BS := (by with_unfolding_all exact (F.BS :))
  BT := (by with_unfolding_all exact (F.BT :))
  ΛS := (by with_unfolding_all exact (F.ΛS :))
  ΛT := (by with_unfolding_all exact (F.ΛT :))
  βS := (by with_unfolding_all exact (F.βS :))
  βT := (by with_unfolding_all exact (F.βT :))
  f₀ := (by with_unfolding_all exact (F.f₀ :))

def tdL {r : ℕ} (G : GlobalTheory.ExportSeries.TypeDat (Dof x) r) : GlobalTheory.ExportSeries.TypeDat (DL x L) r := ⟨(by with_unfolding_all exact (G.Pg :)), (by with_unfolding_all exact (G.P :)), (by with_unfolding_all exact (G.mu :))⟩

def wtL {n : ℕ} (u : GlobalTheory.ExportSeries.Weight (Dof x) n) : GlobalTheory.ExportSeries.Weight (DL x L) n :=
  ⟨(by with_unfolding_all exact (u.p :)), (by with_unfolding_all exact (u.q :)), (by with_unfolding_all exact (u.ap :)), (by with_unfolding_all exact (u.am :)), (by with_unfolding_all exact (u.c :)), (by with_unfolding_all exact (u.lam :))⟩

def baseL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (Z : GlobalTheory.ExportSeries.Base S U) : @GlobalTheory.ExportSeries.Base (DL x L) ((S)) ((U)) where
  hr := (by with_unfolding_all exact (Z.hr :))
  F := frL L Z.F
  G := (by with_unfolding_all exact ((tdL L Z.G) :))
  de := twL L Z.de
  w := (by with_unfolding_all exact ((wtL L Z.w) :))
  mu0 := (by with_unfolding_all exact (Z.mu0 :))
  eta := (by with_unfolding_all exact (Z.eta :))

def setupL (ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw) : GlobalTheory.SeriesTie.Setup (DL x L).ntw where
  rc := ⟨(by with_unfolding_all exact (ρ.rc.κ :)), (by with_unfolding_all exact (ρ.rc.art :))⟩
  ch := (by with_unfolding_all exact (ρ.ch :))
  bad := (by with_unfolding_all exact (ρ.bad :))
  e := (by with_unfolding_all exact (ρ.e :))
  ek := (by with_unfolding_all exact (ρ.ek :))
  B := fun i j b => (by with_unfolding_all exact ((baseL L (ρ.B ((i)) ((j)) b)) : _))
  om := fun i j b χ => (by with_unfolding_all exact ((ρ.om ((i)) ((j)) b ((χ))) : _))
  Cl := fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  finCl := fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  rep := fun i j b t c => (by with_unfolding_all exact ((ρ.rep ((i)) ((j)) b (twB L t) c) : _))
  β := (by with_unfolding_all exact (ρ.β :))
  eG := (by with_unfolding_all exact (ρ.eG :))

theorem twL_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (Dof x) A} (h : t.Good) : (twL L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem twB_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (DL x L) A} (h : t.Good) : (twB L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK_L {Pg Q : Finset (HeightOneSpectrum (𝓞 (Dof x).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (Dof x) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (DL x L) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem placesOK_B {Pg Q : Finset (HeightOneSpectrum (𝓞 (DL x L).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (DL x L) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (Dof x) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem wtL_good {n : ℕ} {u : GlobalTheory.ExportSeries.Weight (Dof x) n} (h : u.Good) : (wtL L u).Good := ⟨(by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.lam_eq :))⟩

theorem thetaFun_L_iff {S U : Formalism.BasicNotions.TH.HSp (Dof x)}
    (F : GlobalTheory.ExportSeries.Frame S U) (f : Formalism.IndefR.Datum.WO S U → ℂ) :
    @Formalism.IndefR.Datum.IsThetaFunO (DL x L) (frL L F).ψ S U f ↔
      @Formalism.IndefR.Datum.IsThetaFunO (Dof x) F.ψ S U f := by
  constructor <;> intro h <;>
    exact ⟨(by with_unfolding_all exact h.quasi),
      (by with_unfolding_all exact h.level),
      (by with_unfolding_all exact h.cont),
      (by with_unfolding_all exact h.smooth)⟩

theorem frL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {F : GlobalTheory.ExportSeries.Frame S U} (h : F.Good) : (frL L F).Good :=
  { rank_le := (by with_unfolding_all exact (h.rank_le :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    sdS := (by with_unfolding_all exact (h.sdS :))
    sdT := (by with_unfolding_all exact (h.sdT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := by
      rcases h.vac with ⟨hstd, hinf, htheta, hlat, hfock, hnorm⟩
      exact ⟨(by with_unfolding_all exact hstd),
        (by with_unfolding_all exact hinf), (by
          exact ⟨(by with_unfolding_all exact htheta.quasi),
            (by with_unfolding_all exact htheta.level),
            (by with_unfolding_all exact htheta.cont),
            (by with_unfolding_all exact htheta.smooth)⟩),
        (by with_unfolding_all exact hlat), (by with_unfolding_all exact hfock),
        (by with_unfolding_all exact hnorm)⟩ }

theorem baseL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {Z : GlobalTheory.ExportSeries.Base S U} (h : Z.Good) : (baseL L Z).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := frL_good L h.frame
    de := twL_good L h.de
    places := (by with_unfolding_all exact ((placesOK_L L h.places) :))
    wt := (by with_unfolding_all exact ((wtL_good L h.wt) :))
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }

theorem setupL_good {ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw} (h : ρ.Good) : (setupL L ρ).Good :=
  { rc := ⟨(by with_unfolding_all exact (h.rc.cont :)), (by with_unfolding_all exact (h.rc.rat :)), (by with_unfolding_all exact (h.rc.loc :)), (by with_unfolding_all exact (h.rc.artin :))⟩
    ch := fun i => ⟨(by with_unfolding_all exact ((h.ch ((i))).pair : _)), (by with_unfolding_all exact ((h.ch ((i))).one : _))⟩
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    base := fun i j b => (by with_unfolding_all exact ((baseL_good L (h.base ((i)) ((j)) b)) : _))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    delta := fun i j b => (by with_unfolding_all exact (congrArg (twL L) (h.delta i j b) : _))
    weil := fun i j b t ht => by
      delta GlobalTheory.ExportSeries.Base.IsWeil
      have hw := h.weil i j b (twB L t) (twB_good L ht)
      have th := thetaFun_L_iff L (ρ.B i j b).F
      refine ⟨(by with_unfolding_all exact hw.std), (by with_unfolding_all exact hw.hecS),
        (by with_unfolding_all exact hw.hecT), (by with_unfolding_all exact hw.resS),
        (by with_unfolding_all exact hw.resT), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p f hf
        exact (th _).2 (hw.om_pres p f ((th _).1 hf))
      · intro g h w f hf
        exact hw.om_heis g h w f ((th _).1 hf)
      · intro g hg g' hg' f hf
        exact hw.om_aut g hg g' hg' f ((th _).1 hf)
      · intro f hf w
        exact hw.om_cont f ((th _).1 hf) w
      · intro μ F hμ hF p f hf
        exact hw.om_unit μ F hμ hF p f ((th _).1 hf)
      · intro e he g h hg hh a b ha hb
        obtain ⟨r, hr, hsplit⟩ := hw.om_split e he g h hg hh a b ha hb
        refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
        apply hsplit ℓ ?_ f ((th _).1 hf)
        intro u hu f' hf'
        exact hℓ u hu f' ((th _).2 hf')
    classes := fun i j b t ht hA =>
      have h' := h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t) (twB_good L ht) ⟨(by with_unfolding_all exact ((placesOK_B L hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩
      ⟨(by with_unfolding_all exact (h'.fin :)), (by with_unfolding_all exact (h'.reps :)), (by with_unfolding_all exact (h'.stab :))⟩ }


open GlobalTheory.SeriesTie in
theorem theta_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).theta = fun i j b h P => (by exact ρ.theta i j b h P) := by
  funext i j b h P
  delta GlobalTheory.SeriesTie.Setup.theta GlobalTheory.ExportSeries.Base.theta GlobalTheory.ExportSeries.Base.vecBase GlobalTheory.ExportSeries.Base.vecAt
    GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  rewrite [GlobalTheory.Mem.R3.Tr.placeModel_eq x.o.Z (oL x L).Z]
  with_unfolding_all exact Eq.refl (ρ.theta i j b h P)


open GlobalTheory.SeriesTie in
theorem isDatum_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsDatum = fun i j b s h P => (by exact ρ.IsDatum i j b s h P) := by
  funext i j b s h P
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.split), (d.off), (d.fin), (d.supp), (d.mem)⟩ : ρ.IsDatum ((i)) ((j)) b ((s)) ((h)) ((P))) : _))
  · exact ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

end GlobalTheory.HeightCounting.Fin3

end
end

