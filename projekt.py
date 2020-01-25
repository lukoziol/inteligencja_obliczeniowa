import random
from pyeasyga import pyeasyga
from collections import deque
import heapq
import copy
import time


'''
    Klasa obsługująca labirynt
    Reprezentacja pól labiryntu:
     - 0 (' ') - puste pole
     - 1 ('#') - ściana
     - 2 ('S') - wejście
     - 3 ('E') - wyjście
     - 4 ('.') - pole ścieżki
     - 5 ('X') - pole odwiedzone algorytmem, które nie należy do znalezionej ściezki
'''
class L:
    # threshold parametrów x*y dla wyswietlania informacji olabiryncie
    __load_print_max = 100000
    __show_print_max = 100000
    __show_progress = True
    __parameters = [
        5.0, # path length
        -2.0, # invalid moves
        -5.0, # repeated position
        -50.0, # final distance from exit
        10000.0 # exit found bonus
        ]


    # --------------------------------------------------------------------------------------------
    '''
        inicjalizacja obiektu
    '''
    def __init__(self, filename, width, height):
        self.__filename = filename
        self.__width = width
        self.__height = height
        self.__wall_count = 0
        self.__path_count = 0

        # flaga wyswietlania danych wczytywania i wyników oraz postepu algorytmu genetycznego
        self.__load_print_flag = (self.__width * self.__height < L.__load_print_max)
        self.__show_print_flag = (self.__width * self.__height < L.__show_print_max)
        self.__progress_print_flag = L.__show_progress

        # tablice danych reprezentujące labirynt i wyniki algorytmów
        self.__data = [[0] * width for i in range(height)]
        self.__bfs = [[0] * width for i in range(height)]
        self.__a_star = [[0] * width for i in range(height)]

        # statystyki algorytmów bfs i A*
        self.__bfs_path_length = 0
        self.__bfs_num_visited = 0        
        self.__a_star_path_length = 0
        self.__a_star_num_visited = 0

        # statystyki i zmienne dla algorytmów genetycznych
        self.__gen_pop = 0
        self.__gen_best = []
        self.__gen_counter = 0        
        self.__gen_current_best = 0

        # załadowanie danych i wyszukanie wejścia/wyjścia labiryntu        
        self.__load()
        self.__mark_entrances()

        # optymalizacja wykonania algorytmów
        # obliczenie odleglosci od wyjścia dla każdego pola
        self.__H_array = [[0] * width for i in range(height)]
        self.__precompute_H_values()
        # obliczenie pozycji wszystkich pustych pól labiryntu (bez wejścia/wyjścia)
        self.__binary_map = []
        self.__precompute_binary_map()
        
        # wyświetlenie wczytanego labiryntu
        self.show()


    # --------------------------------------------------------------------------------------------
    '''
        optymalizacja dla funkcji zawracającej odległość od wyjścia
    '''
    def __precompute_H_values(self):
        for y in range(self.__height):
            for x in range(self.__width):
                self.__H_array[y][x] = ((self.__exit[0] - x)**2 + (self.__exit[1] - y)**2)

    '''
        optymalizacja dla funkcji mapującej gen na puste pola labiryntu
    '''
    def __precompute_binary_map(self):
        for y in range(self.__height):
            for x in range(self.__width):
                if self.__data[y][x] == 0:
                    self.__binary_map.append((x, y))


    # --------------------------------------------------------------------------------------------
    '''
        niektóre wałściwości obiektu są wystawione na zewnątrz jako publiczne interfejsy
    '''
    @property
    def gen_pop(self):
        return self.__gen_pop
    
    @gen_pop.setter
    def gen_pop(self, gen_pop):
        self.__gen_pop = gen_pop

    @property
    def blanks(self):
        return self.__path_count

    @property
    def gen_best_history(self):
        return self.__gen_best


    # --------------------------------------------------------------------------------------------
    '''
        funkcja do resetowania zmiennych algorytmu genetycznego
    '''
    def reset_history(self):
        self.__gen_counter = 0
        self.__gen_best = []
        self.__gen_current_best = None


    '''
        funkcja wczytująca dane, konwersja 3 do 2
    '''
    def __load(self):
        if self.__load_print_flag:
            print('\nFile input')
        f = open(self.__filename, 'r')
        lines = f.readlines()
        for y in range(0, self.__height):
            x, x_tmp = 0, 0
            if self.__load_print_flag:
                print(lines[y][:-1])
            for c in lines[y][:-1]:
                x_tmp += 1
                if x_tmp % 3 != 2:
                    if c != ' ':
                        self.__data[y][x] = 1
                        self.__bfs[y][x] = 1
                        self.__a_star[y][x] = 1
                        self.__wall_count += 1
                    else:
                        self.__data[y][x] = 0
                        self.__bfs[y][x] = 0
                        self.__a_star[y][x] = 0
                        self.__path_count += 1
                    x += 1
        if self.__load_print_flag:
            print('walls: {:d}, pathways: {:d}'.format(self.__wall_count, self.__path_count))


    '''
        funkcja odnajduje wejście i wyjście z labiryntu
        szuka 2 pustych miejsc w obwodzie
        pierwsze puste miejsce to wejście, ostatnie to wyjście
    '''
    def __mark_entrances(self):
        self.__start = None
        self.__exit = None
        # górna krawędź
        for x in range(self.__width):
            if self.__data[0][x] == 0:
                if self.__start is None:
                    self.__start = (x, 0)
                else:
                    self.__exit = (x, 0)
        # krawędzie boczne                
        for y in range(self.__height):
            for x in [0, self.__width - 1]:
                if self.__data[y][x] == 0:
                    if self.__start is None:
                        self.__start = (x, y)
                    else:
                        self.__exit = (x, y)
        # dolna krawędź
        for x in range(self.__width):
            if self.__data[self.__height - 1][x] == 0:
                if self.__start is None:
                    self.__start = (x, self.__height - 1)
                else:
                    self.__exit = (x, self.__height - 1)
        # zapisanie odnalezionych pozycji
        self.__data[self.__start[1]][self.__start[0]] = 2
        self.__data[self.__exit[1]][self.__exit[0]] = 3


    # --------------------------------------------------------------------------------------------
    '''
        standardowe algorytmy przechodzenia labiryntu
    '''
    '''
        algorytm bfs
    '''
    def bfs(self):
        # przygotowanie struktur i inicjalizacja kolejki węzłem startowym
        self.__bfs_path_length = 0
        self.__bfs_num_visited = 0
        visited = [[-1] * self.__width for i in range(self.__height)]
        d = deque()
        p = self.__start
        visited[p[1]][p[0]] = 0
        d.append(p)
        # pętla bfs
        while len(d) > 0:
            p = d.popleft()
            self.__bfs_num_visited += 1            
            self.__bfs[p[1]][p[0]] = 5
            child_depth = visited[p[1]][p[0]] + 1
            moves = []
            moves.append((p[0] + 1, p[1]))
            moves.append((p[0] - 1, p[1]))
            moves.append((p[0], p[1] + 1))
            moves.append((p[0], p[1] - 1))
            for m in moves:
                if 0 <= m[0] < self.__width:
                    if 0 <= m[1] < self.__height:
                        if visited[m[1]][m[0]] == -1:
                            if self.__bfs[m[1]][m[0]] == 0:
                                visited[m[1]][m[0]] = child_depth
                                d.append(m)

        self.__bfs_path_length = visited[self.__exit[1]][self.__exit[0]]
        # pętla rekonstrukcji optymalnej ścieżki (exit -> start)
        p = self.__exit
        while True:
            self.__bfs[p[1]][p[0]] = 4
            moves = []
            moves.append((p[0] + 1, p[1]))
            moves.append((p[0] - 1, p[1]))
            moves.append((p[0], p[1] + 1))
            moves.append((p[0], p[1] - 1))
            if p == self.__start:
                break
            for m in moves:
                if 0 <= m[0] < self.__width:
                    if 0 <= m[1] < self.__height:
                        if self.__bfs[m[1]][m[0]] == 5 and visited[m[1]][m[0]] < visited[p[1]][p[0]]:
                            p = m
                            break

    '''
        algorytm A*
        https://medium.com/@nicholas.w.swift/easy-a-star-pathfinding-7e6689c7f7b2
    '''
    def A_star(self):
        self.__a_star_path_length = 0
        self.__a_star_num_visited = 0
        h = []
        # open = 0, closed = 1
        open_closed = [[-1] * self.__width for i in range(self.__height)]
        visited = [[-1] * self.__width for i in range(self.__height)]
        visited[self.__start[1]][self.__start[0]] = 0        
        # (F, H, pozycja)
        p = self.__start
        heapq.heappush(h, (self.__H_array[p[1]][p[0]], self.__H_array[p[1]][p[0]], p))
        while len(h) > 0:
            (F, H, p) = heapq.heappop(h)
            nG = visited[p[1]][p[0]] + 1
            self.__a_star_num_visited += 1
            self.__a_star[p[1]][p[0]] = 5
            if p == self.__exit:
                break
            open_closed[p[1]][p[0]] = 1
            moves = []
            moves.append((p[0] + 1, p[1]))
            moves.append((p[0] - 1, p[1]))
            moves.append((p[0], p[1] + 1))
            moves.append((p[0], p[1] - 1))
            for m in moves:
                if 0 <= m[0] < self.__width:
                    if 0 <= m[1] < self.__height:
                        if self.__a_star[m[1]][m[0]] == 0:
                            if open_closed[m[1]][m[0]] == -1:
                                # nieodwiedzone
                                nH = self.__H_array[m[1]][m[0]]
                                nF = nH + nG
                                heapq.heappush(h, (nF, nH, m))
                                visited[m[1]][m[0]] = nG
                            elif open_closed[m[1]][m[0]] == 0:
                                # juz w kolejce
                                nH = self.__H_array[m[1]][m[0]]
                                nF = nH + nG
                                for i in range(len(h)):
                                    if h[i][3] == m:
                                        if h[i][1] > nG:
                                            # zamien bo lepsza droga
                                            h[i] = (nF, nH, m)
                                            visited[m[1]][m[0]] = nG
                                        break
        self.__a_star_path_length = visited[self.__exit[1]][self.__exit[0]]
        p = self.__exit
        while True:
            self.__a_star[p[1]][p[0]] = 4
            moves = []
            moves.append((p[0] + 1, p[1]))
            moves.append((p[0] - 1, p[1]))
            moves.append((p[0], p[1] + 1))
            moves.append((p[0], p[1] - 1))
            if p == self.__start:
                break
            for m in moves:
                if 0 <= m[0] < self.__width:
                    if 0 <= m[1] < self.__height:
                        if self.__a_star[m[1]][m[0]] == 5 and visited[m[1]][m[0]] < visited[p[1]][p[0]]:
                            p = m
                            break
            

    # --------------------------------------------------------------------------------------------
    '''
        funkcja wypisująca wyniki trawersowania labiryntów
    '''
    def show(self, mode='map'):
        dataset = None        
        if mode == 'map':            
            print('\nLabyrinth map [{:d} x {:d}]:'.format(self.__width, self.__height))
            dataset = self.__data
        elif mode == 'bfs':
            print('\nBFS path [length = {:d}, visited = {:d}]:'.format(self.__bfs_path_length, self.__bfs_num_visited))
            dataset = self.__bfs
        elif mode == 'a_star':
            print('\nA* path [length = {:d}, visited = {:d}]:'.format(self.__a_star_path_length, self.__a_star_num_visited))
            dataset = self.__a_star
        elif mode =='gene':
            print('\nbest GA path:')
            dataset = self.__gene_map
        if self.__show_print_flag:
            for line in dataset:                
                s = ''.join('{:d}'.format(c) for c in line).replace('0', ' ').replace('1', '#').replace('2', 'S').replace('3', 'E').replace('4', '.').replace('5', 'X')
                print(s)


    # --------------------------------------------------------------------------------------------
    '''
        każda funkcja fitnes dekodująca kroki używa mapowania:
        # 00 -> idź do góry
        # 01 -> idź w lewo
        # 11 -> idź w dół
        # 10 -> idź w prawo

        każda funkcja fitness ma dwie funkcje pomocnicze
         - funkcja wrappera, która pozwala na zebranie statystyk populacji i obliczenie wartosci fitness
         - funkcja renderująca wyniki algorytmu
    '''


    # --------------------------------------------------------------------------------------------
    '''
        obsługa algorytmu genetycznego gdzie chromosomy oznaczają stan każdego pustego pola
    '''
    '''
        funkcja fitness
        - zwraca standardową odległość punktu od wyjścia (jest to punkt na jednorodnej ścieżce najbliższy wyjściu)
        - zwraca ilość nadmiarowych pól względem optymalnej ścieżki bfs (min 0)
    '''
    def fit_binary_fields(self, gene):        
        visited = [[0] * self.__width for i in range(self.__height)]
        visited[self.__start[1]][self.__start[0]] = 1
        visited[self.__exit[1]][self.__exit[0]] = 1
        one_count = 0
        for i in range(len(gene)):
            p = self.__binary_map[i]
            visited[p[1]][p[0]] = gene[i]
            one_count += gene[i]

        d = deque()
        p = self.__start
        d.append(p)        
        min_distance = self.__H_array[p[1]][p[0]]
        while len(d) > 0:
            p = d.popleft()
            min_distance = min(min_distance, self.__H_array[p[1]][p[0]])
            visited[p[1]][p[0]] = 0
            moves = []
            moves.append((p[0] + 1, p[1]))
            moves.append((p[0] - 1, p[1]))
            moves.append((p[0], p[1] + 1))
            moves.append((p[0], p[1] - 1))
            for m in moves:
                if 0 <= m[0] < self.__width:
                    if 0 <= m[1] < self.__height:
                        if visited[m[1]][m[0]] == 1:
                            d.append(m)
        return min_distance, max(0, (one_count - self.__bfs_path_length))

    '''
        wrapper funkcji fitness
    '''
    def fit_binary_fields_wrapper(self, gene, data):
        f_score = self.fit_binary_fields(gene)
        f_distance = f_score[0]
        f_value = -1000 * f_score[0] - f_score[1]

        if self.__gen_counter == 0:
            self.__gen_current_best = (f_value, f_distance)
        else:
            if self.__gen_current_best[0] < f_value:
                self.__gen_current_best = (f_value, f_distance)
                
        self.__gen_counter += 1        
        if self.__gen_counter == self.__gen_pop:
            self.__gen_counter = 0
            self.__gen_best.append(self.__gen_current_best)
            if self.__progress_print_flag:
                print('.', end='')        
        return f_value

    '''
        funkcja przygotowująca ścieżkę zadanego osobnika
    '''
    def predraw_binary_fields(self, best):
        self.__gene_map = copy.deepcopy(self.__data)
        gene = best[1]
        for i in range(len(gene)):
            p = self.__binary_map[i]
            self.__gene_map[p[1]][p[0]] = (gene[i] * 4)


    # --------------------------------------------------------------------------------------------
    '''
        obsługa algorytmu genetycznego gdzie chromosomy oznaczają kroki
        funkcja fitness podąża wyznaczonymi krokami i zatrzymuje się w momencie kolizji
    '''
    '''
        funkcja fitness
        - zwraca standardową odległość punktu końcowego od wyjścia
        - zwraca długość pokonanej ścieżki
    '''
    def fit_collision_ends(self, gene):
        p = self.__start
        path_length = 0
        for i in range(0, len(gene), 2):
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p[0] < 0 or new_p[1] < 0 or new_p[0] >= self.__width or new_p[0] >= self.__height or self.__data[new_p[1]][new_p[0]] != 0:
                break
            p = new_p
            path_length += 1
            if p == self.__exit:
                break
        return self.__H_array[p[1]][p[0]], path_length

    '''
        wrapper funkcji fitness
    '''
    def fit_collision_ends_wrapper(self, gene, data):
        f_score = self.fit_collision_ends(gene)
        f_distance = f_score[0]
        f_value = -f_score[0]

        if self.__gen_counter == 0:
            self.__gen_current_best = (f_value, f_distance)
        else:
            if self.__gen_current_best[0] < f_value:
                self.__gen_current_best = (f_value, f_distance)

        self.__gen_counter += 1        
        if self.__gen_counter == self.__gen_pop:
            self.__gen_counter = 0
            self.__gen_best.append(self.__gen_current_best)
            if self.__progress_print_flag:
                print('.', end='')         
        return f_value

    '''
        funkcja przygotowująca ścieżkę zadanego osobnika
    '''
    def predraw_collision_ends(self, best):
        self.__gene_map = copy.deepcopy(self.__data)
        gene = best[1]        
        p = self.__start
        for i in range(0, len(gene), 2):
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p[0] < 0 or new_p[1] < 0 or new_p[0] >= self.__width or new_p[0] >= self.__height or self.__gene_map[new_p[1]][new_p[0]] != 0:
                break            
            p = new_p
            self.__gene_map[p[1]][p[0]] = 4
            if p == self.__exit:
                break


    # --------------------------------------------------------------------------------------------
    '''
        obsługa algorytmu genetycznego gdzie chromosomy oznaczają kroki
        funkcja fitness podąża wyznaczonymi krokami, kolizje powodują powrót na poprzednie pole
        funkcja zatrzymuje się na koniec sekwencji lub na wyjściu z labiryntu
    '''
    '''
        funkcja fitness
        - zwraca standardową odległość punktu końcowego od wyjścia
        - zwraca długość pokonanej ścieżki
        - zwraca ilość kolizji
    '''
    def fit_collision_stuns(self, gene):
        p = self.__start
        path_length = 0
        collisions = 0
        for i in range(0, len(gene), 2):
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p == self.__exit:
                p = new_p
                path_length += 1
                break
            else:
                if new_p[0] < 0 or new_p[1] < 0 or new_p[0] >= self.__width or new_p[0] >= self.__height or self.__data[new_p[1]][new_p[0]] != 0:
                    collisions += 1
                else:
                    p = new_p
                    path_length += 1
        return self.__H_array[p[1]][p[0]], path_length, collisions

    '''
        wrapper funkcji fitness
    '''
    def fit_collision_stuns_wrapper(self, gene, data):
        f_score = self.fit_collision_stuns(gene)
        f_distance = f_score[0]
        f_value = -f_score[0] - f_score[2]

        if self.__gen_counter == 0:
            self.__gen_current_best = (f_value, f_distance)
        else:
            if self.__gen_current_best[0] < f_value:
                self.__gen_current_best = (f_value, f_distance)
        
        self.__gen_counter += 1        
        if self.__gen_counter == self.__gen_pop:
            self.__gen_counter = 0
            self.__gen_best.append(self.__gen_current_best)
            if self.__progress_print_flag:
                print('.', end='')         
        return f_value

    '''
        funkcja przygotowująca ścieżkę zadanego osobnika
    '''
    def predraw_collision_stuns(self, best):
        self.__gene_map = copy.deepcopy(self.__data)
        gene = best[1]
        p = self.__start
        for i in range(0, len(gene), 2):
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p == self.__exit:
                p = new_p
                self.__gene_map[p[1]][p[0]] = 4
                break
            else:
                if 0 <= new_p[0] < self.__width and 0 <= new_p[1] < self.__height and self.__data[new_p[1]][new_p[0]] == 0:
                    p = new_p
                    self.__gene_map[p[1]][p[0]] = 4


    # --------------------------------------------------------------------------------------------
    '''
        obsługa algorytmu genetycznego gdzie chromosomy oznaczają kroki
        funkcja fitness podąża wyznaczonymi krokami, kolizje powodują powrót na poprzednie pole
        funkcja zlicza ilość kolizji i liczbę powtórzonych pól
        funkcja zatrzymuje się na koniec sekwencji lub na wyjściu z labiryntu
    '''
    '''
        funkcja fitness
        - zwraca standardową odległość punktu końcowego od wyjścia
        - zwraca długość pokonanej ścieżki
        - zwraca ilość kolizji
        - zwraca ilość powtórzonych pól
        - zwraca czy znaleziono wyjście
    '''
    def fit_collision_smart(self, gene):
        visited = [[0] * self.__width for i in range(self.__height)]
        p = self.__start        
        path_length = 0
        collisions = 0
        repetitions = 0
        exit_found = 0        
        for i in range(0, len(gene), 2):
            visited[p[1]][p[0]] = 1
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p == self.__exit:
                p = new_p
                path_length += 1
                exit_found = 1
                break
            else:
                if new_p[0] < 0 or new_p[1] < 0 or new_p[0] >= self.__width or new_p[0] >= self.__height or self.__data[new_p[1]][new_p[0]] != 0:
                    collisions += 1
                else:
                    p = new_p
                    path_length += 1
                    if visited[p[1]][p[0]] == 1:
                        repetitions += 1 
        return self.__H_array[p[1]][p[0]], path_length, collisions, repetitions, exit_found

    '''
        wrapper funkcji fitness
    '''
    def fit_collision_smart_wrapper(self, gene, data):
        f_score = self.fit_collision_smart(gene)
        f_distance = f_score[0]
        f_value = (
            (L.__parameters[0] * f_score[1]) +
            (L.__parameters[1] * f_score[2]) +
            (L.__parameters[2] * f_score[3]) +
            (L.__parameters[3] * f_score[0]) +
            (L.__parameters[4] * f_score[4])
            )  

        if self.__gen_counter == 0:
            self.__gen_current_best = (f_value, f_distance)
        else:
            if self.__gen_current_best[0] < f_value:
                self.__gen_current_best = (f_value, f_distance)

        self.__gen_counter += 1        
        if self.__gen_counter == self.__gen_pop:
            self.__gen_counter = 0
            self.__gen_best.append(self.__gen_current_best)
            if self.__progress_print_flag:
                print('.', end='')          
        return f_value

    '''
        funkcja przygotowująca ściezkę zadanego osobnika
        w tej chwili jest taka sama dla wersji fit_collision_stuns
    '''
    def predraw_collision_smart(self, best):
        self.__gene_map = copy.deepcopy(self.__data)
        gene = best[1]
        p = self.__start        
        for i in range(0, len(gene), 2):
            if gene[i] == 0:
                if gene[i + 1] == 0:
                    new_p = (p[0], p[1] - 1)
                else:
                    new_p = (p[0] - 1, p[1])
            else:
                if gene[i + 1] == 0:
                    new_p = (p[0] + 1, p[1])
                else:
                    new_p = (p[0], p[1] + 1)
            if new_p == self.__exit:
                p = new_p
                self.__gene_map[p[1]][p[0]] = 4
                break
            else:
                if 0 <= new_p[0] < self.__width and 0 <= new_p[1] < self.__height and self.__data[new_p[1]][new_p[0]] == 0:
                    p = new_p
                    self.__gene_map[p[1]][p[0]] = 4


    # --------------------------------------------------------------------------------------------
    '''
        funkcje crossover dla 2 rodzajów opisu genów
    '''
    '''
        funkcja dla opisu binarnego
    '''
    def cross_binary(self, parent_1, parent_2):
        index = random.randrange(1, len(parent_1))
        child_1 = parent_1[:index] + parent_2[index:]
        child_2 = parent_2[:index] + parent_1[index:]
        return child_1, child_2

    '''
        funkcja dla opisu krokowego
    '''
    def cross_steps(self, parent_1, parent_2):
        index = random.randrange(2, len(parent_1))
        if index % 2 != 0:
            index -= 1
        child_1 = parent_1[:index] + parent_2[index:]
        child_2 = parent_2[:index] + parent_1[index:]
        return child_1, child_2


    # --------------------------------------------------------------------------------------------
    
            


# ------------------------------------------------------------------------------------------------
'''
    main
'''

# lista czasów wykonania
times = []

# wczytanie danych
times.append(time.perf_counter_ns())
#lb = L("labirynt_11.txt", 11, 11)
lb = L("labirynt_21.txt", 21, 21)
#lb = L("labirynt_41.txt", 41, 41)
#lb = L("labirynt_61.txt", 61, 61)
#lb = L("labirynt_81.txt", 81, 81)
#lb = L("labirynt_101.txt", 101, 101)
#lb = L("labirynt_201.txt", 201, 201)
times.append(time.perf_counter_ns())

# obliczenie i prezentacja bfs
times.append(time.perf_counter_ns())
lb.bfs()
times.append(time.perf_counter_ns())
lb.show(mode='bfs')

# obliczenie i prezentacja A*
times.append(time.perf_counter_ns())
lb.A_star()
times.append(time.perf_counter_ns())
lb.show(mode='a_star')


# ustawienia dla algorytmow z krokami (mozna uzaleznic od rozmiaru labiryntu)
gnr = 100
pop = 50
steps = lb.blanks * 2


print('\n-------------------------------------------------------------')
print('Algorytm genetyczny - fit_binary_fields')
lb.reset_history()
lb.gen_pop = pop

ga = pyeasyga.GeneticAlgorithm(
    [1] * (lb.blanks - 2),
    population_size=pop,
    generations=gnr,
    mutation_probability=0.95,
    elitism=True
    )
ga.fitness_function = lb.fit_binary_fields_wrapper
ga.crossover_function = lb.cross_binary

times.append(time.perf_counter_ns())
ga.run()
times.append(time.perf_counter_ns())
best = ga.best_individual()

print('\nHistoria najlepszych osobników:\n{}'.format(lb.gen_best_history))
print('Najlepszy osobnik:\n{}'.format(best))
lb.predraw_binary_fields(best)
lb.show(mode='gene')


print('\n-------------------------------------------------------------')
print('Algorytm genetyczny - fit_collision_ends')

lb.reset_history()
lb.gen_pop = pop

ga = pyeasyga.GeneticAlgorithm(
    [0] * steps * 2,
    population_size=pop,
    generations=gnr,
    mutation_probability=0.95,
    elitism=True
    )
ga.fitness_function = lb.fit_collision_ends_wrapper
ga.crossover_function = lb.cross_steps

times.append(time.perf_counter_ns())
ga.run()
times.append(time.perf_counter_ns())
best = ga.best_individual()

print('\nHistoria najlepszych osobników:\n{}'.format(lb.gen_best_history))
print('Najlepszy osobnik:\n{}'.format(best))
lb.predraw_collision_ends(best)
lb.show(mode='gene')


print('\n-------------------------------------------------------------')
print('Algorytm genetyczny - fit_collision_stuns')

lb.reset_history()
lb.gen_pop = pop

ga = pyeasyga.GeneticAlgorithm(
    [0] * steps * 2,
    population_size=pop,
    generations=gnr,
    mutation_probability=0.95,
    elitism=True
    )
ga.fitness_function = lb.fit_collision_stuns_wrapper
ga.crossover_function = lb.cross_steps

times.append(time.perf_counter_ns())
ga.run()
times.append(time.perf_counter_ns())
best = ga.best_individual()

print('\nHistoria najlepszych osobników:\n{}'.format(lb.gen_best_history))
print('Najlepszy osobnik:\n{}'.format(best))
lb.predraw_collision_stuns(best)
lb.show(mode='gene')


print('\n-------------------------------------------------------------')
print('Algorytm genetyczny - fit_collision_smart')

lb.reset_history()
lb.gen_pop = pop

ga = pyeasyga.GeneticAlgorithm(
    [0] * steps * 2,
    population_size=pop,
    generations=gnr,
    mutation_probability=0.95,
    elitism=True
    )
ga.fitness_function = lb.fit_collision_smart_wrapper
ga.crossover_function = lb.cross_steps

times.append(time.perf_counter_ns())
ga.run()
times.append(time.perf_counter_ns())
best = ga.best_individual()

print('\nHistoria najlepszych osobników:\n{}'.format(lb.gen_best_history))
print('Najlepszy osobnik:\n{}'.format(best))
lb.predraw_collision_smart(best)
lb.show(mode='gene')

print('\nCzas wykonania:')
for i, nazwa in zip(range(0, len(times), 2), [
    '      inicjalizacja',
    '                bfs',
    '                 A*',
    '  fit_binary_fields',
    ' fit_collision_ends',
    'fit_collision_stuns',
    'fit_collision_smart']):
    print('{}: {:9.3f}s'.format(nazwa, (times[i + 1] - times[i]) / 1000000000))



