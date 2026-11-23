module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.BarPass

variable {D : D7} {u : D.what₂.Word}

theorem valB_smul_eq {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT)
    (g : M.G) (hg : ∀ v, M.loc v g = 1) (p : M.Pt) : Co.valB w V (g • p) = Co.valB w V p := by
  have h : ∀ v, (g • p).2 v = p.2 v := by
    intro v
    have h1 := M.smul_snd g p v
    rw [hg v] at h1
    apply Subtype.ext
    apply LocF.Raw.ext
    · ext x
      simpa using (h1 x).1
    · funext x
      simpa using (h1 x).2
  unfold PtModel.Coord.valB
  simp only [h]

variable {B : Built.Dat D u} {i : ℕ}

theorem ev_smul (c : D.what₂.LL) (F : B.V i) : B.ev i (c • F) = D.what₂.embLL c • B.ev i F :=
  LinearMap.map_smulₛₗ (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL) c F

theorem isIntegral_torsion {L : Type} [Field L] (ζ : CommGroup.torsion Lˣ) : IsIntegral ℤ ((ζ.1 : Lˣ) : L) := by
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
  refine IsIntegral.of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h]
  exact isIntegral_one

theorem act_zeta_mem {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) {Co : M.Coord}
    (hV : R.ValIs Co) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (b) (d : (B.I.S i).D b) (ζ) (y : M.Val)
    (hy : y ∈ Co.valB w ∅ (R.pt b d)) : M.act (R.zeta ζ) y ∈ Co.valB w ∅ (R.pt b d) := by
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y).1 hy
  refine (hV.dual w hw b d _).2 ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, ev_smul, ← hyF]
    rfl

theorem intBar_of_kerBar : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK _ _ hV hV' hb w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  rw [valB_smul_eq Co w ∅ _ (R.loc_zeta ζ)] at hy
  rw [valB_smul_eq Co' w ∅ _ (R'.loc_zeta ζ')]
  have hy0 := act_zeta_mem R hV hw b d ζ⁻¹ y hy
  have hyy : y = M.act (R.zeta ζ) (M.act (R.zeta ζ⁻¹) y) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  generalize M.act (R.zeta ζ⁻¹) y = y₀ at hy0 hyy
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y₀).1 hy0
  obtain ⟨F', hF', hk⟩ := hb w hw hs b b' d d' F hF
  have hm : B.ev (i + 1) F' ∈ M'.Val := by
    rw [R'.val_eq]
    exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F'
  have h1 : (⟨_, hm⟩ : M'.Val) ∈ Co'.valB w ∅ (R'.pt b' d') := (hV'.dual w hw b' d' _).2 ⟨F', hF', rfl⟩
  refine ⟨_, act_zeta_mem R' hV' hw b' d' ζ' _ h1, ?_⟩
  rw [hyy, K.src, hT, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [hK b b' d d' F y₀ hyF, hk, ev_smul, map_pow, map_natCast]
  rfl

end GlobalTheory.LvT.Built.BarPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
section
noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem levelPrimeDatum_diamond_invariant {E : Type} [Field E] [NumberField E] [StarRing E] (K : Type) [Field K] {n n' : ℕ}
    {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (d' : DecoSet (E := E) (n := n') (ST := ST) (SG := SG')) (P : ST)
    (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) : phiT K (DecoSet.dia1 P a d).1 (DecoSet.dia1 P a d').1 = phiT K d.1 d'.1 := by
  funext x
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun Q => forall_congr' fun y => ?_
  refine imp_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [DecoSet.dia1, DecoSet.dia, Deco.dia]
  exact Units.mul_right_inj _

theorem decoratedLatticePoint_move_diamond {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco ∧
      (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.fr = p.1.1.fr ∧ (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.2 = p.1.2 := by
  have h : p.mv (DecoSet.dia1 P a p.1.1.deco) =
      ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem kAt_dia : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → ∀ b b' d d' (P : Pr.vT u) a, kAt W Ch sel mu cst L A u i b b' ((tdatAt sel mu cst L Tp u i).dia b P a d) ((tdatAt sel mu cst L Tp u (i + 1)).dia b' P a d') = kAt W Ch sel mu cst L A u i b b' d d' := by
  intro X Pr R W Ch sel S mu cst L G m2 u i _ _ _ _ _ Tp A h b b' d d' P a
  obtain ⟨Ξ, -, -, -, -, h⟩ := h b b' d d'
  have key : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p (p.mv (DecoSet.dia1 P a p.1.1.deco)) := by
    intro j p
    obtain ⟨h1, h2, h3⟩ := decoratedLatticePoint_move_diamond p P a
    refine ⟨?_, ?_, h2.symm, h3.symm⟩
    · rw [h1]; exact fun _ _ => rfl
    · rw [h1]; rfl
  have h0 := h d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have h1 := h _ _ (key d) (key d')
  refine h1.trans (Eq.trans ?_ h0.symm)
  rw [(decoratedLatticePoint_move_diamond d P a).1, (decoratedLatticePoint_move_diamond d' P a).1]
  unfold GlobalTheory.KerT.term
  rw [levelPrimeDatum_diamond_invariant]
  rfl

end GlobalTheory.LvT.Built
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section
namespace GlobalTheory.LvT.Built.DilPass

variable {D : D7} {u : D.what₂.Word}

theorem isAct_unique {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n}
    (h₁ : p.IsAct g p₁) (h₂ : p.IsAct g p₂) : p₁ = p₂ := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1]
  · funext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2]

theorem isDil_act {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {a : F}
    {p p' p₁ p₁' : LocF.PP Lc n} (h : LocF.PP.IsDil a p p') (h₁ : p.IsAct g p₁) (h₂ : p'.IsAct g p₁') :
    LocF.PP.IsDil a p₁ p₁' := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  refine ⟨?_, fun x => ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1, h.1]
  · obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2, h.2]

theorem dil_smul {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q : M.Pt} (h : M.Dil v a p q)
    (g : M.G) : M.Dil v a (g • p) (g • q) := by
  refine ⟨M.smul_fst g q p h.1, fun v' hv => ?_, isDil_act h.2.2 (M.smul_snd g p v) (M.smul_snd g q v)⟩
  have h1 := M.smul_snd g q v'
  rw [h.2.1 v' hv] at h1
  exact isAct_unique h1 (M.smul_snd g p v')

theorem dil_unique {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q q' : M.Pt} (h : M.Dil v a p q)
    (h' : M.Dil v a p q') : q = q' := by
  refine Prod.ext (h.1.trans h'.1.symm) (funext fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    apply Subtype.ext
    apply LocF.Raw.ext
    · rw [h.2.2.1, h'.2.2.1]
    · funext x
      rw [h.2.2.2, h'.2.2.2]
  · rw [h.2.1 v' hv, h'.2.1 v' hv]

theorem dil_pt {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    (v : B.ch.A.vT) (a : (B.ch.A.Fv v)ˣ) (b : (B.I.S i).β) (d : (B.I.S i).D b) :
    M.Dil v a (R.pt b d) (R.pt b ((B.J.A i).dia b (B.pr v) a d)) := by
  have hs : ∀ (P : B.ch.A.vT) (x : Fin (D.R.N i) → (M.Lc P).K), ∃ y : Fin (D.R.N i) → B.E, (fun c => R.iK P (y c)) = x :=
    fun P x => ⟨fun c => (R.iK P).symm (x c), funext fun c => by simp⟩
  have hL : ∀ P, ((R.pt b ((B.J.A i).dia b (B.pr v) a d)).2 P).1.L = ((R.pt b d).2 P).1.L := by
    intro P
    ext x
    obtain ⟨y, rfl⟩ := hs P x
    rw [R.pt_L, R.pt_L, (B.hJ.lev i).dia_N b (B.pr v) a d]
  refine ⟨?_, fun v' hv => ?_, hL v, fun x => ?_⟩
  · have h := (R.fst 1 b ((B.J.A i).dia b (B.pr v) a d) d).2
      ⟨1, map_one _, map_one _, by rw [one_smul]; exact (sp.off b).symm (sp.off_dia b d (B.pr v) a)⟩
    rwa [map_one, one_smul] at h
  · apply Subtype.ext
    apply LocF.Raw.ext (hL v')
    funext x
    obtain ⟨y, rfl⟩ := hs v' x
    exact (R.pt_f _ _ v' y).trans ((congrFun (sp.dia_deco b d (B.pr v) (B.pr v') a hv) y).trans (R.pt_f _ _ v' y).symm)
  · obtain ⟨y, rfl⟩ := hs v x
    refine (R.pt_f _ _ v y).trans (((B.hJ.lev i).dia_f b (B.pr v) a d y).trans ?_)
    rw [← R.pt_f b d v y]
    rfl

theorem ext_ev {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ ψ : M.Val →ₗ[ℂ] V)
    (h : ∀ F (y : M.Val), y.1 = B.ev i F → φ y = ψ y) : φ = ψ := by
  have hsp : M.Val = Submodule.span ℂ (Set.range (B.ev i)) := R.val_eq.trans (span_evV _ _ _ _).symm
  ext ⟨y, hy⟩
  have hy' : y ∈ Submodule.span ℂ (Set.range (B.ev i)) := hsp ▸ hy
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, φ ⟨y, hy⟩ = ψ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F, rfl⟩ := hz
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero φ).trans (map_zero ψ).symm
    | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      have hb' : b ∈ M.Val := hsp ▸ hb
      exact (map_add φ ⟨a, ha'⟩ ⟨b, hb'⟩).trans ((congrArg₂ (· + ·) (iha ha') (ihb hb')).trans (map_add ψ ⟨a, ha'⟩ ⟨b, hb'⟩).symm)
    | smul r a ha iha =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      exact (map_smul φ r ⟨a, ha'⟩).trans ((congrArg (r • ·) (iha ha')).trans (map_smul ψ r ⟨a, ha'⟩).symm)
  exact key y hy' hy

theorem dilLaw_of_kerDil : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  intro D u B i sp sp' M M' R R' k K hT hI hD v a p q p' q' h h'
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  have hq := dil_unique M h (dil_smul M (dil_pt R v a b d) (R.zeta ζ))
  have hq' := dil_unique M' h' (dil_smul M' (dil_pt R' v a b' d') (R'.zeta ζ'))
  have h0 : K.k (R.pt b ((B.J.A i).dia b (B.pr v) a d)) (R'.pt b' ((B.J.A (i + 1)).dia b' (B.pr v) a d')) =
      K.k (R.pt b d) (R'.pt b' d') := by
    refine ext_ev R _ _ fun F y hy => Subtype.ext ?_
    rw [hI _ _ _ _ F y hy, hI _ _ _ _ F y hy, hD b b' d d' (B.pr v) a]
  have hs : ∀ y : M.Val, M.act (R.zeta ζ) (M.act (R.zeta ζ)⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hq, hq']
  refine LinearMap.ext fun y => ?_
  rw [← hs y, K.src, K.src, hT, hT, h0]

end GlobalTheory.LvT.Built.DilPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.KerExt

theorem exists_ext {G P T β X : Type} [Group G] [MulAction G P] [Group T] {H D : β → Type} [∀ b, Group (H b)]
    [∀ b, MulAction (H b) (D b)] (ρ : G → X → X) (ρ1 : ∀ x, ρ 1 x = x) (ρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (pt : ∀ b, D b → P) (hom : ∀ b, H b →* G) (zeta : T →* G)
    (pt_smul : ∀ b g d, pt b (g • d) = hom b g • pt b d)
    (gen : ∀ b (g : G), ∃ ζ g', g = zeta ζ * hom b g')
    (comm : ∀ ζ (g : G), zeta ζ * g = g * zeta ζ)
    (surj : ∀ p : P, ∃ ζ b d, p = zeta ζ • pt b d)
    (idx : ∀ ζ b b' d d', zeta ζ • pt b d = pt b' d' → b = b')
    (inj : ∀ ζ b d d', zeta ζ • pt b d = pt b d' → ∃ g : H b, g • d = d' ∧ ∀ x, ρ (hom b g) x = ρ (zeta ζ) x)
    (φ : ∀ b, D b → X) (hφ : ∀ b g d, φ b (g • d) = ρ (hom b g) (φ b d)) :
    ∃ Φ : P → X, (∀ b d, Φ (pt b d) = φ b d) ∧ ∀ g p, Φ (g • p) = ρ g (Φ p) := by
  have key : ∀ g ζ b d ζ' b' d', g • zeta ζ • pt b d = zeta ζ' • pt b' d' →
      ρ (zeta ζ') (φ b' d') = ρ g (ρ (zeta ζ) (φ b d)) := by
    intro g ζ b d ζ' b' d' h
    obtain ⟨ζ₀, g₀, rfl⟩ := gen b g
    have e : zeta (ζ'⁻¹ * ζ₀ * ζ) * hom b g₀ = (zeta ζ')⁻¹ * (zeta ζ₀ * hom b g₀ * zeta ζ) := by
      rw [map_mul, map_mul, map_inv, mul_assoc, comm ζ]
      simp only [mul_assoc]
    have h1 : zeta (ζ'⁻¹ * ζ₀ * ζ) • pt b (g₀ • d) = pt b' d' := by
      rw [pt_smul, ← mul_smul, e, mul_smul, mul_smul, h, inv_smul_smul]
    obtain rfl := idx _ _ _ _ _ h1
    obtain ⟨g₁, rfl, hg⟩ := inj _ _ _ _ h1
    rw [hφ, hg, hφ, ← ρm, ← ρm, ← ρm, mul_assoc, e, mul_inv_cancel_left]
  choose z i d hp using surj
  refine ⟨fun p => ρ (zeta (z p)) (φ (i p) (d p)), fun b x => ?_, fun g p => ?_⟩
  · have := key 1 1 b x (z (pt b x)) (i (pt b x)) (d (pt b x)) (by rw [← hp, map_one, one_smul, one_smul])
    exact this.trans (by rw [map_one, ρ1, ρ1])
  · exact key g (z p) (i p) (d p) _ _ _ (by rw [← hp, ← hp])

theorem exists_cplx {K V V' W W' : Type} [Field K] (σ : K →+* ℂ) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : V →ₛₗ[σ] W) (e' : V' →ₛₗ[σ] W')
    (li : LinearIndependent ℂ fun j => e (Module.Basis.ofVectorSpace K V j))
    (sp : Submodule.span ℂ (Set.range e) = ⊤) (f : V →ₗ[K] V') :
    ∃ fC : W →ₗ[ℂ] W', ∀ F, fC (e F) = e' (f F) := by
  set b := Module.Basis.ofVectorSpace K V
  have hmem : ∀ F, e F ∈ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have sp' : ⊤ ≤ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    rw [← sp, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact hmem F
  let c := Module.Basis.mk li sp'
  refine ⟨c.constr ℂ fun j => e' (f (b j)), fun F => ?_⟩
  have h : (c.constr ℂ fun j => e' (f (b j))).comp e = e'.comp f := by
    refine b.ext fun j => ?_
    have : e (b j) = c j := by simp [c]
    simp only [LinearMap.comp_apply, this, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h F

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

def evM : B.V i →ₛₗ[D.what₂.embLL] M.Val :=
  LinearMap.codRestrict M.Val (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL)
    fun F => by rw [R.val_eq]; exact evV_mem_ValC _ _ _ _ F

theorem evM_li : LinearIndependent ℂ fun j => evM R (Module.Basis.ofVectorSpace D.what₂.LL (B.V i) j) :=
  LinearIndependent.of_comp M.Val.subtype
    (evV_linearIndependent B.emb 1 (B.lam i) D.what₂.embLL (fr0 B.emb D.what₂.embLL _) _
      (Module.Basis.ofVectorSpace D.what₂.LL (B.V i)).linearIndependent)

theorem evM_span : Submodule.span ℂ (Set.range (evM R)) = ⊤ := by
  apply Submodule.map_injective_of_injective M.Val.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact (span_evV B.emb 1 (B.lam i) D.what₂.embLL).trans R.val_eq.symm

theorem evM_rho (b) (g : (B.I.S i).G b) (F : B.V i) :
    evM R ((B.I.S i).rho B.emb (B.lam i) b g F) = M.act (R.hom b g) (evM R F) := by
  apply Subtype.ext
  rw [R.act_hom]
  exact GStep.evV_rho_eq_tr _ _ _ _ b g F

theorem inj_act (ζ b d d') (h : R.zeta ζ • R.pt b d = R.pt b d') :
    ∃ g : (B.I.S i).G b, g • d = d' ∧ M.act (R.hom b g) = M.act (R.zeta ζ) := by
  obtain ⟨g, h1, h2, h3⟩ := (R.inj ζ b d d').1 h
  refine ⟨g, h3, LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [R.act_hom, R.act_zeta]
  funext x
  refine (trFr_apply B.emb D.what₂.embLL ((B.I.S i).gam b g) ((B.I.S i).chr b g) y.1 x).trans ?_
  rw [h1, h2, inv_one, frMul_one]
  rfl

theorem inj_act_inv (ζ b) (g : (B.I.S i).G b) (h : M.act (R.hom b g) = M.act (R.zeta ζ)) :
    M.act (R.hom b g)⁻¹ = M.act (R.zeta ζ)⁻¹ := by
  calc M.act (R.hom b g)⁻¹ = M.act (R.hom b g)⁻¹ * (M.act (R.zeta ζ) * M.act (R.zeta ζ)⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = _ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ext_evM {W : Type} [AddCommGroup W] [Module ℂ W] {f g : M.Val →ₗ[ℂ] W} (h : ∀ F, f (evM R F) = g (evM R F)) :
    f = g :=
  LinearMap.ext_on_range (evM_span R) h

end Real

theorem exists_kerPt : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  intro D u B i sp sp' M M' R R' k hk
  choose kC hkC using fun b b' d d' =>
    exists_cplx D.what₂.embLL (evM R) (evM R') (evM_li R) (evM_span R) (k b b' d d')
  have hequiv : ∀ b b' (g : (B.I.S i).G b) (g' : (B.I.S (i + 1)).G b') d d',
      kC b b' (g • d) (g' • d') = M'.act (R'.hom b' g') ∘ₗ kC b b' d d' ∘ₗ M.act (R.hom b g)⁻¹ := by
    intro b b' g g' d d'
    refine ext_evM R fun F => ?_
    rw [hkC, hk.equiv, ← map_inv]
    simp only [LinearMap.comp_apply]
    rw [evM_rho, ← evM_rho R, hkC]

  have h1 : ∀ b d, ∃ Φ : M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b' d', Φ (R'.pt b' d') = kC b b' d d') ∧
      ∀ (g : M'.G) p, Φ (g • p) = M'.act g ∘ₗ Φ p := by
    intro b d
    refine exists_ext (fun (g : M'.G) (x : M.Val →ₗ[ℂ] M'.Val) => M'.act g ∘ₗ x) ?_ ?_ R'.pt R'.hom R'.zeta R'.pt_smul
      R'.gen R'.comm R'.surj (fun ζ b b' d d' h => R'.idx ζ b b' d d' (congrArg Prod.fst h)) ?_
      (fun b' d' => kC b b' d d') ?_
    · intro x
      simp only [map_one]
      rfl
    · intro g h x
      simp only [map_mul]
      rfl
    · intro ζ b' d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R' ζ b' d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [h2]⟩
    · intro b' g d'
      have := hequiv b b' 1 g d d'
      rw [one_smul, map_one, inv_one, map_one] at this
      exact this
  choose Φ hΦ hΦe using h1

  obtain ⟨Ψ, hΨ, hΨe⟩ : ∃ Ψ : M.Pt → M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b d, Ψ (R.pt b d) = Φ b d) ∧
      ∀ (g : M.G) p, Ψ (g • p) = fun p' => Ψ p p' ∘ₗ M.act g⁻¹ := by
    refine exists_ext (fun (g : M.G) (x : M'.Pt → (M.Val →ₗ[ℂ] M'.Val)) p' => x p' ∘ₗ M.act g⁻¹) ?_ ?_ R.pt R.hom R.zeta
      R.pt_smul R.gen R.comm R.surj (fun ζ b b' d d' h => R.idx ζ b b' d d' (congrArg Prod.fst h)) ?_ Φ ?_
    · intro x
      simp only [inv_one, map_one]
      rfl
    · intro g h x
      simp only [mul_inv_rev, map_mul]
      rfl
    · intro ζ b d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R ζ b d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [inj_act_inv R ζ b g h2]⟩
    · intro b g d
      funext p'
      obtain ⟨ζ, b', d', rfl⟩ := R'.surj p'
      have := hequiv b b' g 1 d d'
      rw [one_smul, map_one, map_one] at this
      simp only [hΦe, hΦ, this]
      rfl
  have hpt : ∀ b b' d d', Ψ (R.pt b d) (R'.pt b' d') = kC b b' d d' := fun b b' d d' => by rw [hΨ, hΦ]
  refine ⟨⟨Ψ, fun g p p' y => ?_, fun c c' y => ?_⟩, fun g' p p' y => ?_, fun b b' d d' F y hy => ?_⟩
  · rw [hΨe]
    show Ψ p p' ((M.act g⁻¹ * M.act g) y) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [R.rep_eq, R'.rep_eq, hpt]
    have : B.ch.C.Kmap i c c' ∘ₗ M.Val.subtype =
        M'.Val.subtype ∘ₗ kC c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') := by
      refine ext_evM R fun F => ?_
      simp only [LinearMap.comp_apply]
      rw [hkC]
      exact hk.kmap c c' F
    exact LinearMap.congr_fun this y
  · obtain ⟨ζ, b, d, rfl⟩ := R.surj p
    show Ψ _ _ y = M'.act g' (Ψ _ _ y)
    simp only [hΨe, hΨ, hΦe]
    rfl
  · obtain rfl : y = evM R F := Subtype.ext hy
    show (Ψ _ _ _).1 = _
    rw [hpt, hkC]
    rfl

end GlobalTheory.LvT.Built.KerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem trueCols_exists_primitiveRoots : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  intro B X I h l Z i
  have hP := (base_fields_primes_ok B X).2.1
  have hf : 0 < B.fields.f := by
    have e : B.fields.f = 2 * B.R.ord := B.fields_f
    have := B.R.ord_pos
    rw [e]; omega
  exact colRoots_exists_primitiveRoots B.fields (B.primes X) B.R.m I.Ch hf hP h.ch_ok i

end GlobalTheory
end

