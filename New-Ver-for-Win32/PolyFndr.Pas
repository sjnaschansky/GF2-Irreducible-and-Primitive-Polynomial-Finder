{

Copyright (C) 2015 SN

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
may be used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
OF THE POSSIBILITY OF SUCH DAMAGE.

}

{$A+,B-,D+,E+,F-,G-,I+,L+,N-,O-,P-,Q-,R-,S+,T-,V+,X+,Y+}
{$M 1024,0,0}

{На будущее.}
{1. Вспомогательные полиномы удобнее хранить сдвинутыми к старшему биту, нежели к младшему как это используется сейчас.}
{   Такое выравнивание позволит исключить сдвиги при подготовке к проверке на делимость и упростить деление.}
{   Проблемным в этом случае может стать полином x, но его можно не включать в таблицы.}
{2. Добавить сохранение вспомогательных полиномов в файл и их загрузку из файла.}
{   Имеет смысл сделать 3 режима: Compute, Compute&Save и Load.}

Program PolyFndr;
  {========================================================================================================================}

{Программа расчёта неприводимых полиномов.}
{Компилятор FPC 2.6.0.}

Label
  {========================================================================================================================}
  {Метки первого ассемблерного блока.}
  MaskLoop, PolySave_OuterLoop, OuterLoop, InnerLoop,
  DividerError, NotEnouthMemoryError, SeachCompleted,

  GF2DivisionTest32, GF2DivisionTest32_Loop, GF2DivisionTest32_Loop_NoXOR, GF2DivisionTest32_ClrZF_Pop_Ret,
  GF2DivisionTest32_Pop_Ret, GF2DivisionTest32_Ret,

  DifferenceUpdateAndPolySave,
  PolySave,
  GetLimForDiv32,
  GetMSB32, GetMSB32_NoInc,

  ASMExit,

  {========================================}
  {Метки второго ассемблерного блока.}
  StartValLoop64, PolySearchOuterLoop64, PolySearchInnerLoop64, DividerError64, SeachCompleted64,

  GF2DivisionTest64, GF2DivisionTest64_BigShift, GF2DivisionTest64_SkipBigShift, GF2DivisionTest64_Loop,
  GF2DivisionTest64_EDXTest, GF2DivisionTest64_SkipEDXTest, GF2DivisionTest64_Loop_NoXOR, GF2DivisionTest64_ClrZF_PopX2_Ret,
  GF2DivisionTest64_Pop_Ret, GF2DivisionTest64_Ret,

  GetMSB32_2, GetMSB32_2_NoInc,

  ASMExit64;

Const
  {========================================================================================================================}
  {Количество элементов массива, который используется для хранения вспомогательных полиномов, 32 бита на полином.}
  Poly32QtyMax          = 1048576 * 40;

  {Количество элементов массива, который используется для хранения рабочих полиномов, 64 бита на полином.}
  Poly64QtyMax          = 1024;

Type
  {========================================================================================================================}
  {Определение массивов.}
  Poly32ArrayType       = Array [0 .. Poly32QtyMax - 1] Of LongInt;
  Poly64ArrayType       = Array [0 .. (Poly64QtyMax * 2) - 1] of LongInt;

  {Определение указателей на эти массивы.}
  Poly32ArrayPtrType    = ^Poly32ArrayType;
  Poly64ArrayPtrType    = ^Poly64ArrayType;

Var
  {========================================================================================================================}
  {Указатель на массив вспомогательных полиномов.}
  Poly32ArrayPtr        : Poly32ArrayPtrType;
  {Указатель на массив рабочих полиномов.}
  Poly64ArrayPtr        : Poly64ArrayPtrType;
  {Порядок рабочих полиномов.}
  Poly64Order           : Byte;
  {Счётчик цикла, нужен для вывода полиномов на экран.}
  Counter               : LongInt;

  {========================================}
  {Переменные 1-го ассемблерного блока.}
  MaskForEnd32          : LongInt;
  AsmBlock1_ExitCode    : Byte;
  DifferenceMax32       : LongInt;
  LastPoly32            : LongInt;
  PolyCounter32         : LongInt;

  {========================================}
  {Переменные 2-го ассемблерного блока.}
  Poly64Qty             : LongInt;
  Poly64MSB             : Byte;
  AsmBlock2_ExitCode    : Byte;
  PolyCounter64         : LongInt;

  {========================================}
  {Переменные 3-го ассемблерного блока.}
  AsmBlock3_ExitCode    : Byte;

  {========================================}
  {Отладка.}
  Debug_EAX, Debug_EBX  : LongInt;
  Debug_ECX, Debug_EDX  : LongInt;
  Debug_ESI, Debug_EDI  : LongInt;
  Debug_ESP, Debug_EBP  : LongInt;

{========================================================================================================================}
{Процедура печати полинома степени до 63-й включительно.}
{Для печати полиномов степени до 31-й включительно устанавливать DataH в 0.}
{Процедура написана с нуля, без оглядки на оригинальный код.}
Procedure Poly64WriteLn (DataH, DataL : Longint);
Var
  I : Byte;
  LSB, Data_H, Data_L : Longint;
  S, S2 : String;
Begin
  Data_H := DataH;
  Data_L := DataL;
  S := '';
  For I := 0 To 63 Do Begin
    LSB := Data_L And $1;
    asm {Сдвиг вправо на 1 бит 64-х битного значения в Data_H:Data_L.}
      pushf
      push  eax
      mov   eax, Data_H
      shr   eax, 1
      mov   Data_H, eax
      mov   eax, Data_L
      rcr   eax, 1
      mov   Data_L, eax
      pop   eax
      popf
    end;
    If LSB = 1 Then Begin {Формирование текстовой строки.}
      If I = 0 Then S := '1' + S;
      If I = 1 Then If S = '' Then S := 'x' + S Else S := 'x+' + S;
      If I > 1 Then Begin
        Str (I, S2);
        If S = '' Then S := 'x^' + S2 + S Else S := 'x^' + S2 + '+' + S;
        End;
      End;
    End;
  WriteLn (S);
End;

  {Тесты.}
  {Poly64WriteLn (0, 255);
  Poly64WriteLn (0, 128);
  Poly64WriteLn (0, 1);
  Poly64WriteLn (1, 1);}

{========================================}
{Процедура печати переменных в шестнадцатеричном виде.}
Procedure Hex32WriteLn (Data : Longint);
Const
  Symbols : Array [0 .. 15] of Char = ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
Var
  S : String;
Begin
  S := '0x' + Symbols [(Data shr 28) And $F] + Symbols [(Data shr 24) And $F] + Symbols [(Data shr 20) And $F]
            + Symbols [(Data shr 16) And $F] + Symbols [(Data shr 12) And $F] + Symbols [(Data shr  8) And $F]
            + Symbols [(Data shr  4) And $F] + Symbols [(Data       ) And $F];
  WriteLn (S);
End;

{========================================}
{Процедура печати переменных в шестнадцатеричном виде.}
Procedure Hex64WriteLn (DataH, DataL : Longint);
Const
  Symbols : Array [0 .. 15] of Char = ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
Var
  S : String;
Begin
  S := '0x' + Symbols [(DataH shr 28) And $F] + Symbols [(DataH shr 24) And $F] + Symbols [(DataH shr 20) And $F]
            + Symbols [(DataH shr 16) And $F] + Symbols [(DataH shr 12) And $F] + Symbols [(DataH shr  8) And $F]
            + Symbols [(DataH shr  4) And $F] + Symbols [(DataH       ) And $F];
  S := S    + Symbols [(DataL shr 28) And $F] + Symbols [(DataL shr 24) And $F] + Symbols [(DataL shr 20) And $F]
            + Symbols [(DataL shr 16) And $F] + Symbols [(DataL shr 12) And $F] + Symbols [(DataL shr  8) And $F]
            + Symbols [(DataL shr  4) And $F] + Symbols [(DataL       ) And $F];
  WriteLn (S);
End;

{========================================}
{Процедура печати значений регистров процессора.}
Procedure PrintRegs;
Begin
  Write ('EAX = '); Hex32WriteLn (Debug_EAX);
  Write ('EBX = '); Hex32WriteLn (Debug_EBX);
  Write ('ECX = '); Hex32WriteLn (Debug_ECX);
  Write ('EDX = '); Hex32WriteLn (Debug_EDX);
  Write ('ESI = '); Hex32WriteLn (Debug_ESI);
  Write ('EDI = '); Hex32WriteLn (Debug_EDI);
  Write ('ESP = '); Hex32WriteLn (Debug_ESP);
  Write ('EBP = '); Hex32WriteLn (Debug_EBP);
End;

{========================================}
{Отладочный код, вставить в требуемое место.}
    {mov   Debug_EAX, eax
    mov   Debug_EBX, ebx
    mov   Debug_ECX, ecx
    mov   Debug_EDX, edx
    mov   Debug_ESI, esi
    mov   Debug_EDI, edi
    mov   Debug_ESP, esp
    mov   Debug_EBP, ebp}

Begin
{========================================================================================================================}

  {Выделение памяти.}
  {Функция Length не учитывает то, что каждый элемент массива Poly32ArrayType состоит из 4-х байтов, т.е. надо домножить на 4.}

  GetMem(Poly32ArrayPtr, Length (Poly32ArrayType) * 4);
  GetMem(Poly64ArrayPtr, Length (Poly64ArrayType) * 4);

  Poly64Order := 53;

  {Измерение времени расчёта проводилось на процессоре Intel Atom N270 с помощью программы Process Explorer v14.1, приведён параметр Total Time.}
  {Порядки 62 и 63: вспомогательные полиномы до 31-го порядка включительно, всего их 143522117, максимальная разница 528, 238137s грубое измерение.}
  {Порядки 60 и 61: вспомогательные полиномы до 30-го порядка включительно, всего их  74248451, максимальная разница 476, 98720s грубое измерение.}
  {Порядки 58 и 59: вспомогательные полиномы до 29-го порядка включительно, всего их  38458184, максимальная разница 432, 32567s.}
  {Порядки 56 и 57: вспомогательные полиномы до 28-го порядка включительно, всего их  19945394, максимальная разница 388, 13559s.}
  {Порядки 54 и 55: вспомогательные полиномы до 27-го порядка включительно, всего их  10358999, максимальная разница 368, 4688s.}
  {Порядки 52 и 53: вспомогательные полиномы до 26-го порядка включительно, всего их   5387991, максимальная разница 368, 1968s.}
  {Порядки 50 и 51: вспомогательные полиномы до 25-го порядка включительно, всего их   2807196, максимальная разница 324, 689s.}
  {Порядки 48 и 49: вспомогательные полиномы до 24-го порядка включительно, всего их   1465020, максимальная разница 324.}
  {Порядки 46 и 47: вспомогательные полиномы до 23-го порядка включительно, всего их    766150, максимальная разница 226.}
  {Порядки 44 и 45: вспомогательные полиномы до 22-го порядка включительно, всего их    401428, максимальная разница 198.}
  {Порядки 42 и 43: вспомогательные полиномы до 21-го порядка включительно, всего их    210871, максимальная разница 198.}
  {Порядки 40 и 41: вспомогательные полиномы до 20-го порядка включительно, всего их    111013, максимальная разница 180.}
  {Порядки 38 и 39: вспомогательные полиномы до 19-го порядка включительно, всего их     58636, максимальная разница 136.}
  {Порядки 36 и 37: вспомогательные полиномы до 18-го порядка включительно, всего их     31042, максимальная разница 132.}
  {Порядки 34 и 35: вспомогательные полиномы до 17-го порядка включительно, всего их     16510, максимальная разница 124.}
  {Порядки 32 и 33: вспомогательные полиномы до 16-го порядка включительно, всего их      8800, максимальная разница 124.}
  {Порядки 30 и 31: вспомогательные полиномы до 15-го порядка включительно, всего их      4720, максимальная разница  82.}
  {Порядки 28 и 29: вспомогательные полиномы до 14-го порядка включительно, всего их      2538, максимальная разница  68.}
  {Порядки 26 и 27: вспомогательные полиномы до 13-го порядка включительно, всего их      1377, максимальная разница  62.}
  {Порядки 24 и 25: вспомогательные полиномы до 12-го порядка включительно, всего их       747, максимальная разница  62.}
  {Порядки 22 и 23: вспомогательные полиномы до 11-го порядка включительно, всего их       412, максимальная разница  38.}
  {Порядки 20 и 21: вспомогательные полиномы до 10-го порядка включительно, всего их       226, максимальная разница  30.}
  {Порядки 18 и 19: вспомогательные полиномы до  9-го порядка включительно, всего их       127, максимальная разница  30.}
  {Порядки 16 и 17: вспомогательные полиномы до  8-го порядка включительно, всего их        71, максимальная разница  30.}
  {Порядки 14 и 15: вспомогательные полиномы до  7-го порядка включительно, всего их        41, максимальная разница  16.}
  {Порядки 12 и 13: вспомогательные полиномы до  6-го порядка включительно, всего их        23, максимальная разница  14.}
  {Порядки 10 и 11: вспомогательные полиномы до  5-го порядка включительно, всего их        14, максимальная разница   8.}
  {Порядки  8 и  9: вспомогательные полиномы до  4-го порядка включительно, всего их         8, максимальная разница   6.}

  {========================================================================================================================}
  asm
    {Сохранение флагов и используемых регистров.}
    pushf
    pushad
    {========================================}

    {Вычисление маски, по которой будет завершаться поиск вспомогательных полиномов.}
    xor   ecx, ecx
    xor   eax, eax
    mov   cl, Poly64Order
    shr   ecx, 1
    inc   ecx

    {Тело цикла вычисления маски.}
  MaskLoop:
    stc
    adc   eax, eax
    loop  MaskLoop

    mov   MaskForEnd32, eax

    {========================================}

    {Инициализация поиска.}
    cld
    mov   edi, Poly32ArrayPtr
    xor   ebx, ebx
    mov   AsmBlock1_ExitCode, 0
    mov   DifferenceMax32, 0

    mov   eax, 2 {Первый неприводимый полином - x, и имеет представление 2.}
    call  PolySave {Этот полинoм сохраняется, но не используется т.к. из-за увеличения EAX каждый раз на 2, проверять делимость на него не нужно.}

    mov   eax, 3 {Второй неприводимый полином - x + 1, и имеет представление 3.}
    call  DifferenceUpdateAndPolySave

    mov   eax, 7 {Третий неприводимый полином - x^2 + x + 1, и имеет представление 7.}
  PolySave_OuterLoop:
    call  DifferenceUpdateAndPolySave

    {Цикл в котором производится поиск.}
  OuterLoop:

    inc   eax {Получение очередного полинома для проверки.}
    test  eax, MaskForEnd32 {Здесь же проверка на достижение заданного полинома.}
    jz    SeachCompleted
    inc   eax

    cmp   ebx, Poly32QtyMax {Проверка на полное заполнение таблицы, по ошибке выход, код 1.}
    jnc   NotEnouthMemoryError {Эта проверка должна идти 2-й по счёту, т.к. окончание поиска при полном заполнении таблицы не является ошибкой.}

    call  GetLimForDiv32

    mov   esi, Poly32ArrayPtr
    lea   esi, [esi + 4] {Пропуск первого полинома.}

  InnerLoop:

    mov   edx, [esi]
    lea   esi, [esi + 4]

    cmp   ebp, edx
    jc    PolySave_OuterLoop

    call  GF2DivisionTest32
    jz    DividerError {Выход по ошибке деления, код 2.}
    jnc   OuterLoop
    jmp   InnerLoop

    {Обработка особых ситуаций.}
  DividerError:
    inc   AsmBlock1_ExitCode
  NotEnouthMemoryError:
    inc   AsmBlock1_ExitCode
  SeachCompleted:
    mov   PolyCounter32, ebx

    jmp   ASMExit

    {========================================}
    {Подпрограммы.}

    {========================================}
    {Процедура проверки на деление полинома в EAX на полином в EDX.}
    {ZF = 1, ошибка; ZF = 0, CF = 0 деление без остатка; ZF = 0, CF = 1 деление с остатком.}
    {EAX, EBX - сохраняются; ECX, EDХ - не сохраняются; ESI, EDI, EBP - не используются.}
  GF2DivisionTest32:

    xor   ecx, ecx

    call  GetMSB32
    jz    GF2DivisionTest32_Ret {ZF установлен.}

    xchg  eax, edx
    xchg  cl, ch

    call  GetMSB32
    jz    GF2DivisionTest32_Ret {ZF установлен.}

    xchg  eax, edx
    xchg  cl, ch

    push  eax
    push  ebx

    xor   ebx, ebx
    mov   bl, cl
    sub   cl, ch
    jc    GF2DivisionTest32_Pop_Ret {ZF сброшен, CF установлен.}
    xor   ch, ch

    {Подготовка делителя в EDX.}
    shl   edx, cl

    inc   cl

    {Само деление EAX на EDX.}
  GF2DivisionTest32_Loop:
    dec   ebx
    bt    eax, ebx
    jnc   GF2DivisionTest32_Loop_NoXOR
    xor   eax, edx
    jz    GF2DivisionTest32_ClrZF_Pop_Ret {ZF установлен, CF сброшен, перед выходом нужно сбросить ZF.}
  GF2DivisionTest32_Loop_NoXOR:
    shr   edx, 1
    loop  GF2DivisionTest32_Loop

    stc {Установка CF.}

  GF2DivisionTest32_ClrZF_Pop_Ret:
    inc   ebx {Сброс ZF, CF не затрагивается}

  GF2DivisionTest32_Pop_Ret:
    pop   ebx
    pop   eax
  GF2DivisionTest32_Ret:
    ret

    {========================================}
    {Процедура вычисления максимума разности 2-х соседних полиномов, если рассматривать их как двоичные числа и сохранения полинома.}
  DifferenceUpdateAndPolySave:

    mov   edx, eax
    sub   edx, LastPoly32
    cmp   DifferenceMax32, edx
    jnc   PolySave
    mov   DifferenceMax32, edx

    {========================================}
    {Процедура сохранения полинома.}
  PolySave:

    mov   LastPoly32, eax
    stosd
    inc   ebx

    ret

    {========================================}
    {Процедура определения граничного полинома, до достижения которого будет выполняться деление.}
  GetLimForDiv32:

    call   GetMSB32
    xor    ebp, ebp
    inc    cl
    shr    cl, 1
    bts    ebp, ecx

    ret

    {========================================}
    {Процедура вычисления номера старшего ненулевого разряда в регистре EAX, оптимизированная через инструкцию BSR.}
  GetMSB32:

    push  eax

    xor   cl, cl
    bsr   eax, eax
    jz    GetMSB32_NoInc
    inc   al
    mov   cl, al
  GetMSB32_NoInc:

    pop   eax
    ret

    {========================================}

  ASMExit:
    {========================================}
    {Восстановление используемых регистров и флагов.}
    popad
    popf
  end;
  {========================================================================================================================}

  WriteLn ('AsmBlock1_ExitCode = ', AsmBlock1_ExitCode);
  WriteLn ('DifferenceMax32 = ', DifferenceMax32);
  WriteLn ('LastPoly32 = ', LastPoly32);
  WriteLn ('PolyCounter32 = ', PolyCounter32);

  If (AsmBlock1_ExitCode <> 0) Then Halt (AsmBlock1_ExitCode);

  {========================================================================================================================}

  Poly64Qty := Poly64QtyMax;

  {Рассчитанные полиномы проверялись на совпадение с данными из файлов s1.txt, s2.txt, s3.txt, s4.txt, s5.txt и показали полное совпадение.}

  {========================================================================================================================}
  asm
    {Сохранение флагов и используемых регистров.}
    pushf
    pushad
    {========================================}

    {Вычисление начального значения для поиска полиномов.}
    xor   ecx, ecx
    xor   eax, eax
    xor   edx, edx
    mov   cl, Poly64Order
    inc   cl
    mov   Poly64MSB, cl {Все полиномы, которые будут тестироваться, имеют один порядок, поэтому положение старшего бита можно вычислить один раз в начале.}
    dec   cl

    {Тело цикла вычисления начального значения.}
  StartValLoop64:
    stc
    adc   eax, eax
    adc   edx, edx
    loop  StartValLoop64

    {========================================}

    {Инициализация поиска.}
    mov   AsmBlock2_ExitCode, 0
    mov   PolyCounter64, 0

    {Цикл в котором производится поиск.}
  PolySearchOuterLoop64:

    add   eax, 2 {Получение очередного полинома для проверки.}
    mov   esi, Poly32ArrayPtr {Здесь же подготовка адреса таблицы проверочных полиномов.}
    adc   edx, 0
    lea   esi, [esi + 4]
    xor   ebx, ebx {Т.к. первый полином пропускается, EBX сразу нужно установить в 1.}
    inc   ebx

  PolySearchInnerLoop64:

    mov   edi, [esi]
    lea   esi, [esi + 4]

    call  GF2DivisionTest64
    jz    DividerError64 {Выход по ошибке деления, код 2.}
    jnc   PolySearchOuterLoop64

    inc   ebx
    cmp   ebx, PolyCounter32 {Проверка на достижение конца таблицы вспомогательных полиномов.}
    jc    PolySearchInnerLoop64

    mov   ecx, PolyCounter64 {Конец таблицы достигнут, найденный полином неприводимый, сохранение его в таблице.}
    lea   edi, [ecx * 8]
    add   edi, Poly64ArrayPtr
    mov   [edi + 0], eax
    mov   [edi + 4], edx

    inc   ecx {Проверка на достижение конца основной таблицы.}
    cmp   ecx, Poly64Qty
    mov   PolyCounter64, ecx

    jz    SeachCompleted64
    jmp   PolySearchOuterLoop64

    {Обработка особых ситуаций.}
  DividerError64:
    inc   AsmBlock2_ExitCode
    inc   AsmBlock2_ExitCode
  SeachCompleted64:

    jmp   ASMExit64

    {========================================}
    {Подпрограммы.}

    {========================================}
    {Процедура проверки на деление полинома в EDX:EAX на полином в EDI.}
    {ZF = 1, ошибка; ZF = 0, CF = 0 деление без остатка; ZF = 0, CF = 1 деление с остатком.}
    {EAX, EBX, EDX, ESI - сохраняются; ECX, EDI, EBP - не сохраняются.}
  GF2DivisionTest64:

    xor   ecx, ecx

    call  GetMSB32_2
    jz    GF2DivisionTest64_Ret {ZF установлен.}

    mov   ch, cl
    mov   cl, Poly64MSB

    push  esi
    push  ebx
    xor   esi, esi
    xor   ebx, ebx

    mov   bl, cl
    sub   cl, ch
    jc    GF2DivisionTest64_Pop_Ret {ZF сброшен, CF установлен.}
    xor   ch, ch

    {Подготовка делителя в ESI:EDI.}
    cmp   cl, 31 {Эта проверка нужна т.к. команда shld не умеет сдвигать более чем на 31 разряд.}
    ja    GF2DivisionTest64_BigShift
    shld  esi, edi, cl
    shl   edi, cl
    jmp   GF2DivisionTest64_SkipBigShift
  GF2DivisionTest64_BigShift:
    mov   esi, edi
    xor   edi, edi
    shl   esi, cl
  GF2DivisionTest64_SkipBigShift:

    inc   cl
    push  edx
    push  eax

    {Само деление EDX:EAX на ESI:EDI.}
  GF2DivisionTest64_Loop:
    dec   ebx
    cmp   ebx, 31 {Эта проверка нужна т.к. старший бит может быть и в EDX и в EAX.}
    ja    GF2DivisionTest64_EDXTest
    bt    eax, ebx
    jmp   GF2DivisionTest64_SkipEDXTest
  GF2DivisionTest64_EDXTest:
    bt    edx, ebx
  GF2DivisionTest64_SkipEDXTest:
    jnc   GF2DivisionTest64_Loop_NoXOR
    xor   edx, esi {!!! Здесь в оригинальном коде выявлена ошибка, связанная с использованием команды setnz. !!!}
    xor   eax, edi {!!! Ноль в EDX:EAX определялся не верно, фактически определялся ноль только в EAX. !!!}
    mov   ebp, edx {!!! Т.к. делимое всегда содержит единицу при 0-й степени, а делитель не превосходит 31-ю степень, то неправильный результат не возникал. !!!}
    or    ebp, eax {EBP = 0 если и EDX и EAX = 0.}
    jz    GF2DivisionTest64_ClrZF_PopX2_Ret  {ZF установлен, CF сброшен, перед выходом нужно сбросить ZF.}
  GF2DivisionTest64_Loop_NoXOR:
    shr   esi, 1
    rcr   edi, 1
    loop  GF2DivisionTest64_Loop

    stc {Установка CF.}

  GF2DivisionTest64_ClrZF_PopX2_Ret:
    inc   ebx {Сброс ZF, CF не затрагивается}

    pop   eax
    pop   edx

  GF2DivisionTest64_Pop_Ret:
    pop   ebx
    pop   esi
  GF2DivisionTest64_Ret:
    ret

    {========================================}
    {Процедура вычисления номера старшего ненулевого разряда в регистре EDI, оптимизированная через инструкцию BSR.}
  GetMSB32_2:

    push  eax
    mov   eax, edi

    xor   cl, cl
    bsr   eax, eax
    jz    GetMSB32_2_NoInc
    inc   al
    mov   cl, al
  GetMSB32_2_NoInc:

    pop   eax
    ret

    {========================================}

  ASMExit64:
    {========================================}
    {Восстановление используемых регистров и флагов.}
    popad
    popf
  end;
  {========================================================================================================================}

  WriteLn ('AsmBlock2_ExitCode = ', AsmBlock2_ExitCode);
  WriteLn ('Poly64MSB = ', Poly64MSB);
  For Counter := 0 To (Poly64Qty - 1) Do Hex64WriteLn (Poly64ArrayPtr^[Counter * 2 + 1], Poly64ArrayPtr^[Counter * 2 + 0]);
  For Counter := 0 To (Poly64Qty - 1) Do Poly64WriteLn (Poly64ArrayPtr^[Counter * 2 + 1], Poly64ArrayPtr^[Counter * 2 + 0]);

  If (AsmBlock2_ExitCode <> 0) Then Halt (AsmBlock2_ExitCode);

  ReadLn;

  {Коды возврата из ассемблерных блоков устанавливаются в 0.}
  AsmBlock3_ExitCode := 0;

End.
