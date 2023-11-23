\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{TemplateExercise}

%%%% PERSONALIZATION %%%%

\newcommand{\mName}{\texttt{\textbackslash{}renewcommand\{\textbackslash{}mName\}\{<Name(s)>\}}}
\newcommand{\Semester}{\texttt{\textbackslash{}renewcommand\{\textbackslash{}Semester\}\{<Semester>\}}}
\newcommand{\LectureName}{\texttt{\textbackslash{}renewcommand\{\textbackslash{}LectureName\}\{<Lecture>\}}}
\newcommand{\SheetName}{\texttt{\textbackslash{}renewcommand\{\textbackslash{}SheetName\}\{<Sheet>\}}}


\LoadClass[11pt,a4paper]{scrartcl}

%%%% PACKAGES %%%%

\RequirePackage{acronym}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amstext}
\RequirePackage{amsthm}
\RequirePackage{algorithm}
\RequirePackage{algpseudocode}
\RequirePackage{booktabs}
\RequirePackage[english]{babel}
\RequirePackage{calc}
\RequirePackage{color}
\RequirePackage{dsfont}
\RequirePackage{enumerate}
\RequirePackage[shortlabels]{enumitem}
\RequirePackage{environ}
\RequirePackage{etoolbox}
\RequirePackage{float}
\RequirePackage[T1]{fontenc}
\RequirePackage{geometry}
\RequirePackage{graphicx}
\RequirePackage{imakeidx}
\RequirePackage[utf8]{inputenc}
\RequirePackage{listings}
\RequirePackage{lmodern}
\RequirePackage{mathrsfs}
\RequirePackage{mathtools}
\RequirePackage{nicefrac}
\RequirePackage{pifont}
\RequirePackage{pgf,tikz}
\RequirePackage{pgfplots}
\RequirePackage{qrcode}
\RequirePackage[figuresleft]{rotating}
\RequirePackage{scrextend}
\RequirePackage[headsepline]{scrlayer-scrpage}
\RequirePackage{selinput}
\RequirePackage{setspace}
\RequirePackage{subcaption}
\RequirePackage{soul}
\RequirePackage{stmaryrd}
\RequirePackage{tabularx}
\RequirePackage[most]{tcolorbox}
\usetikzlibrary{calc}
\RequirePackage{tkz-euclide}
\RequirePackage[
  %colorlinks=true,
  urlcolor=black, linkcolor=black]{hyperref}
\geometry{a4paper, top=20mm, left=25mm, right=25mm, bottom=20mm, headsep=5mm, footskip=12mm}
% \usetkzobj{all}
\setlist{listparindent=\parindent}

%%%% LAYOUT %%%%

\ofoot{\today}
\ifoot{\LectureName}
\cfoot{\thepage}
\ihead{\textsc{\SheetName}}
\ohead{\textsc{\mName}}

\title{\vspace{-1cm} \SheetName}
\author{}
\date{}

\AtBeginDocument{
\maketitle
\vspace*{-2.5cm}
\thispagestyle{scrheadings}
}

%%%% MACROS %%%%

\DeclarePairedDelimiter\ceil{\lceil}{\rceil}
\DeclarePairedDelimiter\floor{\lfloor}{\rfloor}

\newcommand{\IN}{\mathbb{N}}
\newcommand{\IZ}{\mathbb{Z}}
\newcommand{\IQ}{\mathbb{Q}}
\newcommand{\IR}{\mathbb{R}}
\newcommand{\IC}{\mathbb{C}}
\newcommand{\IP}{\mathbb{P}}
\newcommand{\IK}{\mathbb{K}}
\newcommand{\IL}{\mathbb{L}}
\newcommand{\IF}{\mathbb{F}}
\newcommand{\IV}{\mathbb{V}}
\newcommand{\IS}{\mathbb{S}}
\newcommand{\IE}{\mathbb{E}}
\newcommand{\cmark}{\text{\ding{51}}}
\newcommand{\xmark}{\text{\ding{55}}}
\newcommand{\ggT}{\textnormal{ggT}}
\newcommand{\kgV}{\textnormal{kgV}}
\newcommand{\charac}{\textnormal{char}}
\newcommand{\set}[1]{\left\lbrace#1\right\rbrace}
\newcommand{\Span}[1]{\left<#1\right>}
\newcommand{\Scalar}{\Span{\cdot,\cdot}}
\newcommand{\BLF}{\textnormal{BLF}}
\newcommand{\intervalcc}[1]{\left[#1\right]}
\newcommand{\intervalco}[1]{\left[#1\right)}
\newcommand{\intervaloc}[1]{\left(#1\right]}
\newcommand{\intervaloo}[1]{\left(#1\right)}
\newcommand{\entspr}{\widehat{=}}
\newcommand{\range}{\textnormal{range}}
\newcommand{\rd}{\textnormal{rd}}
\newcommand{\eps}{\textnormal{eps}}
\newcommand{\enquote}[1]{\glqq{}#1\grqq{}}
\newcommand{\Mor}{\textnormal{Mor}}
\newcommand{\Hom}{\textnormal{Hom}}
\newcommand{\End}{\textnormal{End}}
\newcommand{\Abb}{\textnormal{Abb}}
\newcommand{\Ker}{\textnormal{Ker}}
\newcommand{\Img}{\textnormal{Im}}
\newcommand{\bij}{\overset{\sim}{\to}}
\newcommand{\surj}{\twoheadrightarrow}
\newcommand{\inj}{\hookrightarrow}
\newcommand{\iso}{\cong}
\newcommand{\id}{\textnormal{id}}
\newcommand{\rg}{\textnormal{rg}}
\newcommand{\dist}{\textnormal{dist}}
\newcommand{\diag}{\textnormal{diag}}
\newcommand{\Gl}{\textnormal{Gl}}
\newcommand{\Bij}{\textnormal{Bij}}
\newcommand{\ord}{\textnormal{ord}}
\newcommand{\sgn}{\textnormal{sgn}}
\newcommand{\abs}[1]{\left|#1\right|}
\newcommand{\norm}[1]{\left\|#1\right\|}
\newcommand{\transp}[1]{\begin{pmatrix}\begin{smallmatrix}#1\end{smallmatrix}\end{pmatrix}}
\newcommand{\EV}{\textnormal{EV}}
\newcommand{\EW}{\textnormal{EW}}
\newcommand{\idx}{\textnormal{index}}
\newcommand{\NST}{\textnormal{NST}}
\newcommand{\tr}{\textnormal{tr}}
\newcommand{\Unif}{\textnormal{Unif}}
\newcommand{\Lin}{\textnormal{Lin}}
\newcommand{\Bin}{\textnormal{Bin}}
\newcommand{\Pf}{\textnormal{Pf}}
\newcommand{\Sp}{\textnormal{Sp}}
\newcommand{\Sl}{\textnormal{Sl}}
\newcommand{\Var}{\textnormal{Var}}
\newcommand{\1}{\mathds{1}}
\newcommand{\epi}{\textnormal{epi}}
\newcommand{\SO}{\textnormal{SO}}
\newcommand{\Coker}{\textnormal{Coker}}
\newcommand{\Ob}{\textnormal{Ob}}
\newcommand{\grad}{\nabla}
\newcommand{\Exp}{\textnormal{Exp}}
\newcommand{\Coim}{\textnormal{Coim}}
\newcommand{\supp}{\textnormal{supp}}
\newcommand{\Real}{\textnormal{Re}}
\newcommand{\Sym}{\textnormal{Sym}}

\newcommand{\breakline}[1]{%
    \begingroup%
        \par\centering\bfseries%
        \rule[0.6ex]{1.5cm}{1pt} #1 \rule[0.6ex]{1.5cm}{1pt}\par%
    \endgroup%
}

%%%% THEOREMS %%%%


\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollar}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{problem}[theorem]{Problem}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\numberwithin{equation}{section}
\numberwithin{theorem}{section}

%%%% MISC %%%%

\pgfplotsset{compat=1.15}

\usetikzlibrary{arrows}
\usetikzlibrary{shapes, arrows.meta, positioning}
\SelectInputMappings{
  adieresis={ä},
  germandbls={ß}
}
\usetikzlibrary{cd}

\makeatletter
\def\namedlabel#1#2{\begingroup
   \def\@currentlabel{#2}%
   \label{#1}\endgroup
}
\makeatother


\setcounter{MaxMatrixCols}{20}

\setlength\parindent{0pt}
\setlength\parskip{5pt plus1pt minus1pt}

% \numberwithin{equation}{section}

\algrenewcommand\algorithmicrequire{\textbf{Input:}}
\algrenewcommand\algorithmicensure{\textbf{Output:}}
% \algnewcommand\algorithmicappend{\textpf{append}}