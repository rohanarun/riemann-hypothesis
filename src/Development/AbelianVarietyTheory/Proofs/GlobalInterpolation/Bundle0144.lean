module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLattices
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
section
open NumberField IsDedekindDomain

noncomputable section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (degAt degNu)

namespace GlobalTheory.ChainTheta

section Step

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hadd : A.IndAdd a b Sa D) (hsm : A.IndSmooth a b Sa D)
    (hrat : ∀ N N' c x, InRange Sa D c N N' x → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sa D (c * c') N N' x) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sa N N')) (mulLat (c * c') (homAt Sa N N')) fun y =>
        thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := latFin X a b Sa N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite
    (↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)
  set rep := fun z : ↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective
      ((mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)) z :
      ↥(mulLat c (homAt Sa N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sa D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sa N N' c x = fun w => ∑ z, A.thInd Sa N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have hJ : jetOp lam lam' (A.jetK Sa N N' c x) n =
      jetOp lam lam' (fun m => ∑ z, A.jetK Sa N N' (c * c') (x + rep z) m) n := by
    refine GlobalTheory.JetIdentity.jetOp_congr lam lam' n _ _ fun m hm => ?_
    have h2 : derivAt0 (A.thInd Sa N N' c x) m = ∑ z, derivAt0 (A.thInd Sa N N' (c * c') (x + rep z)) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
      rw [Finset.sum_apply, _root_.sum_apply]
    choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
    have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m = A.σ₀ (∑ z, k z) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hk]
      unfold jetC
      rw [h2, Finset.mul_sum, Finset.mul_sum]
    unfold Amb.jetK
    rw [h3, desc_map]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← hk z, desc_map]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, Formalism.L2.Ker.jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

end Step

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) (j : ℕ) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hL : A.LaHyp (R.N i) (R.N j) (Sall sel mu u)) (hE : A.ESmooth (R.N i) (R.N j))
    (hrat : ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar X.Tau (R.N i) (R.N j) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (W.lamTrue u i) (nuLast W u i) τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF _ _ N N')⁻¹ * jetC A.cD (A.thInd (Sall sel mu u) N N' c x) m)
    (hR : RatStep W Ch sel mu cst A u i j) :
    ThDist.Ok (stepC W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  have hD := modulus_pos sel mu cst u hT
  unfold RatStep at hR
  rw [← stepC_eq_stepT W Ch sel mu cst hq A u i hi] at hR
  exact
    { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A _ _ sel _ _ _ _ _ _ N fr N' fr' c x x' h
      add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
        thDistC_add_deg A _ _ _ sel _ _ _ _ _
          (indAdd_of A _ _ _ _ hD (latFin X _ _ _) (indTieD_of_la A _ _ _ _ hD hL)) (indSmooth_of A _ _ _ _ hE) hrat
          N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
      equiv := thDistC_equiv A _ _ sel _ _ _ _ _ _ hD _ _ hR
      det := fun N fr N' fr' c x κ κ' _ _ =>
        thDistC_det A _ _ sel _ _ _ _ _ _ _ _ (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _)
          (unitInv_rho Ch sel mu i) N fr N' fr' c x κ κ' }

end Chain

theorem chTh_ok_of_hyp {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} (B : Base H cc δ) {χ : TaylorLogMetric.IdE H → ℂ}
    {cD : H.what₂.Tau → ℂ} {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
    {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word} {m2 : ℕ} (hm : Z.R.m = m2 + 2)
    (h : Hyp Z s cc δ χ cD sel S mu cst u) (hE : B.EqP χ) (hV : B.VecP χ) (hq : MuqTie Z.Ch sel mu cst)
    (hJ : ∀ i, i < Z.R.m → ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) →
      ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ *
        jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) :
    ChTh.Ok (Ch := Z.Ch) cst (chTh Z.W Z.Ch sel mu cst (ambOf s B χ cD) u m2) := by
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes Z.X Z.Pr sel S mu u h.ok.fields h.ok.primes h.isSel h.T_mem h.g_mem
  have key : ∀ i j, i < Z.R.m → j = i + 1 →
      ThDist.Ok (stepC Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (Z.W.lamTrue u j)) (Sall sel mu u)
        (cAof sel mu cst * cBof sel mu cst u) ((rhoVr Z.X.emb (Z.W.lamTrue u i)).comp (ufGL Z.X.E (Z.R.N i)))
        ((rhoVr Z.X.emb (Z.W.lamTrue u j)).comp (ufGL Z.X.E (Z.R.N j))) (rhoS Z.Ch sel mu i) (rhoT Z.Ch sel mu i) := by
    rintro i _ hi rfl
    obtain ⟨hL, hS⟩ := _root_.GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth H Z.X s cc δ B χ cD (Z.R.N i) (Z.R.N (i + 1)) h.ok.fields h.ana.1 h.ana.2.2.1 h.ana.2.2.2.1 hV
      (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _) (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _)
    exact stepC_ok_deg Z.W Z.Ch sel mu cst _ u i hi (i + 1) (h.ok.primes.T_prime u).pos hq
      ⟨hL.1, hL.2.1, fun P hP => (bad P hP).1,
        fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one Z.X H s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (h.cop P hP),
        hL.2.2.2.2⟩ hS (hJ i hi)
      (_root_.GlobalTheory.KerT.RatLaw.ratStep Z H s cc δ B χ cD sel S mu cst u i hi h hE hV hq (hJ i hi))
  exact ⟨fun i hi => key i (i + 1) (by omega) rfl, key (m2 + 1) Z.R.m (by omega) hm⟩


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi)
    (a : I.ι) (u : B.Word) (m2 : ℕ) (hm : B.R.m = m2 + 2) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2) := by
  have h1 := chTh_ok_of_hyp (Z := I.dat) (I.J.toRec B C W V S N G) hm (hyp_of_colIn B C W V S N G I h a u) hE hV
    (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) (by
      rw [← AmbIn.amb_eq_ambOf]
      intro i hi L L' c x hx m hd
      refine hJ.exists_eq hi hx fun τ => ?_
      rw [monoDeg_eq_sum]
      exact (hd τ).trans (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi τ))
  rw [← AmbIn.amb_eq_ambOf] at h1
  exact h1


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn' (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) :=
  chTh_ok_of_colIn B C W V S N G I h hJ hE hV a u _ h.hm

end GlobalTheory.ChainTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
section
noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def bP (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m - 1)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
    Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g

def bM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g

def coP (u : B.Word) (a : I.ι) (w : B.places.Pl) :
    ((I.perIn u a).S'.Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ]
      ((I.perIn u a).S'.Cl → MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m - 1) × Fin (B.R.N B.R.m - 1)) ℂ) :=
  LinearMap.pi fun c =>
    actP (I.perIn u a).sgT (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bP I u a w c)⁻¹)) ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ
      LinearMap.proj c

def coM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    (Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) →ₗ[ℂ]
      MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m) × Fin (B.R.N B.R.m)) ℂ :=
  actP (lamT (B.hcW u) B.R.m) (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bM I u a w c)⁻¹)) ∘ₗ
    polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m)) ∘ₗ
    (((I.chIn u a).S B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)).toLinearMap

end GlobalTheory.PerQ.Co

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (M : PtModel B.ch i) (R : B.Real i sp M), i ≤ D.R.m → B.Sees → ∃ Co : M.Coord, Co.Ok ∧ R.ValIs Co := by
  first | exact @GlobalTheory.LvT.Built.ValLat.exists_coord | exact GlobalTheory.LvT.Built.ValLat.exists_coord | (intros; apply GlobalTheory.LvT.Built.ValLat.exists_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerDecTwTOfStd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem perDecTwT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) (Y : DivX (I.rec7 l Z)), I.StdTw l Z l0 t → ∀ u a ha, GlobalTheory.PerQ.PerDecTwT Y t u a ha := by
  intro B X I hI l Z l0 hR cf nch tp C t Y hS u a ha x hx F hF c
  have hP := (t.ptE.per u a ha).2.2
  classical
  have hres : ∀ z, GlobalTheory.PerQ.resCTw t u a ha c z = fun c' => if c' = c then z c' else 0 := by
    intro z
    apply (t.pt.val u a ha).eW.injective
    rw [GlobalTheory.PerQ.resCTw, LinearEquiv.apply_symm_apply]
    funext c' s
    have e1 := hS.2.2.eW u a ha (fun c' => if c' = c then z c' else 0) c' s s rfl
    have e2 := hS.2.2.eW u a ha z c' s s rfl
    refine Eq.trans ?_ e1.symm
    split_ifs
    all_goals first | exact e2 | rfl | (exfalso; contradiction)
  obtain ⟨y, hy, hyv⟩ := hR.tw u a F hF c
  have hyQ : y ∈ nabAt B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c)) := by
    have := GlobalTheory.PeriodOnStep.Lsh_eq_N ((I.stX a).rep c).1.1.deco
    show y ∈ nabAt _ _ (((I.stX a).rep c).1.1.deco.1.Lsh)
    rw [this]; exact hy
  obtain ⟨b, hb⟩ := @_root_.GlobalTheory.PairAtClass.pair_integral _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL _ _ (I.perIn u a) (l.ch u a) (l.per u a) (B.hcW u)
    (l.fmL u a).famP (((I.rec7 l Z).eMtTw u a).symm F) (t.ptE.jM u a (((I.rec7 l Z).eMtTw u a).symm F))
    (fun w => hP w _) c (fun p q => Classical.propDecidable (p = q)) y hyQ hyv x hx
  refine ⟨(b : B.fields.K), ?_, fun w _ => ?_⟩
  · show B.embLL (b : B.fields.K) = _
    rw [hb, GlobalTheory.PerQ.pcLTw, hres, hres]
    rfl
  · by_cases h0 : (b : B.fields.K) = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      unfold vAdd
      have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := (I.rec7 l Z).what₂.LL) ((I.rec7 l Z).plEq w) b
      have h2 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 h
      rw [WithZero.log_one] at h2
      exact neg_nonneg.mpr h2

end GlobalTheory.PerTwClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem trueWeights_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I _ l Z u a τ
  have hc : Formalism.MainNotions.product_first_zeroth_parts.cTw B.R = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    have h2 : 2 ∣ B.R.t + 1 := B.R.t_odd.add_one.two_dvd
    unfold Formalism.MainNotions.product_first_zeroth_parts.cTw
    rw [Nat.mul_div_assoc _ h2]
    push_cast; rfl
  have key : ∀ {n : ℕ} (w : DomWeight n), Formalism.MainNotions.product_first_zeroth_parts.wSh w (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
      GlobalTheory.Mem.Col2.shW w (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) := by
    intro n w
    unfold Formalism.MainNotions.product_first_zeroth_parts.wSh GlobalTheory.Mem.Col2.shW
    congr 1
    funext i
    rw [hc]; ring
  have hs : ∀ τ, (I.perIn u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hw := GlobalTheory.LvT.BuiltChain.weights_ok (I.perIn u a) (B.hcW u) B.fields.emb hs
  refine ⟨key _, key _, (hw τ).1, (hw τ).2, fun τ' i => ?_⟩
  obtain ⟨ha, hb⟩ := (hw τ').1 i
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW] at ha hb
  constructor
  · show (B.wts.sgW τ').w i ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩
    change 0 ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ').w i + _) at hb
    linarith
  · show (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ').w i
    change 0 ≤ (B.wts.sgW τ').w i + _ - ((Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
    linarith

end GlobalTheory.PerQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VAddNonnegOfInt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerDecAtRef


open Formalism.BasicNotions in
theorem vAdd_nonneg_of_int {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : 0 ≤ vAdd la (a : K) := by
  have h : la.valuation K (a : K) ≤ 1 := la.valuation_le_one a
  unfold vAdd
  rcases eq_or_ne (la.valuation K (a : K)) 0 with h0 | h0
  · rw [h0, WithZero.log_zero]; simp
  · have h1 : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp h0]
      simpa using h
    exact neg_nonneg.mpr h1

end GlobalTheory.PerDecAtRef


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PerDecAtRef.perDec0At_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.MainNotions.RT.PeriodPointConditions.PerDec0At F := by
  intro B X I hI l Z hZ u Ch chOf F hF
  intro x hx G hG c
  classical
  obtain ⟨y0, hy0, hrd⟩ := hZ.ref u G hG c
  have hpr : ∀ w, ((I.perIn u I.mu0).per B.fields.emb B.embLL (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)).period w
      (((I.rec7 l Z).eMt u).symm G) = (I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0)
      (F.jM (((I.rec7 l Z).eMt u).symm G)) w := by
    intro w
    have hper := F.per
    unfold Formalism.L2.Forms.PerTie at hper
    exact hper.2.2 w _
  have key := _root_.GlobalTheory.PairAtClass.pair_integral B.fields.emb B.embLL (I.perIn u I.mu0) (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)
    (l.fmL u I.mu0).famP (((I.rec7 l Z).eMt u).symm G) (F.jM (((I.rec7 l Z).eMt u).symm G)) hpr c y0 ?ha ?hb
  case ha =>
    clear hpr hZ hI hx hG hrd hF
    have hL : (I.perIn u I.mu0).S'.Lsh c.fst ((I.perIn u I.mu0).S'.rep c) = (((I.stX I.mu0).rep c).1.1.deco).1.N :=
      GlobalTheory.PeriodOnStep.Lsh_eq_N _
    rw [hL]
    exact hy0
  case hb =>
    clear hpr hZ hI hx hG hy0 hF
    convert hrd using 2
  obtain ⟨a, ha⟩ := key x hx
  refine ⟨(a : B.fields.K), ?_, ?_⟩
  · have hw := hF.eW
    have hsingle : ∀ (dec : ∀ c' : ((I.rec7 l Z).fm u).clsP, Decidable (c' = c)) (v : ((I.rec7 l Z).mem u).P.Wrow),
        F.valP.eW.symm (fun c' => @ite _ (c' = c) (dec c') (F.valP.eW v c') 0) =
          fun (c' : (I.perIn u I.mu0).S'.Cl) => if c' = c then v c' else 0 := by
      intro dec v
      apply F.valP.eW.injective
      rw [LinearEquiv.apply_symm_apply]
      funext c' s
      erw [hw _ c' s ⟨s.1, s.2⟩ rfl]
      by_cases h : c' = c
      · rw [if_pos h, if_pos (show @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        erw [hw v c' s ⟨s.1, s.2⟩ rfl]
      · rw [if_neg h, if_neg (show ¬ @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        rfl
    unfold Formalism.MainNotions.RT.PeriodPointConditions.pcL Formalism.MainNotions.RT.PeriodPointConditions.resC
    rw [hsingle, hsingle]
    clear key hpr hrd hy0 hG hZ hI hx hsingle hw hF
    refine ha.trans ?_
    congr! 4
    exact congrArg (fun f => ⇑((I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0) f))
      (funext fun c' => by by_cases h : c' = c <;> simp [h])
  · intro w
    right
    exact GlobalTheory.PerDecAtRef.vAdd_nonneg_of_int _ a
end

